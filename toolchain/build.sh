### BUILDS A RISCV TOOLCHAIN USING CROSSTOOL-NG ###

# stop on errors
set -e

# configuration
CROSSTOOL_VERSION=1.24.0-rc3
HELP2MAN_VERSION=1.47.10
TEXINFO_VERSION=6.6
PKGCONFIG_VERSION=1.1.0

if [ "$#" -lt 1 ] || [ ! -f "$1" ]; then
    echo "Fatal error: expects at least a single argument with crosstool config"
    exit
fi
if [ -z "$RISCV" ]; then
    echo "Fatal error: set RISCV to install location of the toolchain"
    exit
fi

# FIXME: install dependencies for crosstool-ng if not found on host
# help2man might be missing, install it temporary if it is missing
export PATH=$PATH:$(pwd)/install/bin/
if ! command -v help2man >/dev/null 2>&1; then
    echo "Not having help2man, installing a temporary version for crosstool..."
    curl https://ftp.gnu.org/gnu/help2man/help2man-$HELP2MAN_VERSION.tar.xz | tar -xJp
    cd help2man-$HELP2MAN_VERSION/
    ./configure --prefix=$(pwd)/../install
    make -j$(nproc)
    make install
    cd ..
fi
# makeinfo might be missing, install it temporary if it is missing
if ! command -v makeinfo >/dev/null 2>&1; then
    echo "Not having texinfo, installing a temporary version for crosstool..."
    curl https://ftp.gnu.org/gnu/texinfo/texinfo-$TEXINFO_VERSION.tar.xz | tar -xJp
    cd texinfo-$TEXINFO_VERSION/
    ./configure --prefix=$(pwd)/../install
    make -j$(nproc)
    make install
    cd ..
fi

mkdir -p $RISCV
# download and install crosstool-ng
if [ ! -x "$RISCV/bin/ct-ng" ]; then
    chmod -R u+w $RISCV
    echo "No crosstool-ng found, installing..."
    curl http://crosstool-ng.org/download/crosstool-ng/crosstool-ng-$CROSSTOOL_VERSION.tar.xz | tar -xJp
    cd crosstool-ng-$CROSSTOOL_VERSION
    ./configure --prefix=$RISCV
    if [ ! $? -eq 0 ]; then
        echo "Fatal error: failed to configure crosstool-ng"
	      exit
    fi
    cd ..
    make -C crosstool-ng-$CROSSTOOL_VERSION
    make -C crosstool-ng-$CROSSTOOL_VERSION install
fi

# symlink the local patches directory in the configs to be used during build
# FIXME: currently only hardcoded patches directory will be used
if [ ! -L "patches" ]; then
    echo "Symlinking patches directory to build directory"
    conf_dir=$(readlink -f $(dirname "$1"))
    ln -s $conf_dir/patches $(pwd)/patches
fi

# initialize the configuration
echo "Initializing toolchain build..."
cp "$1" .config
mkdir -p src
echo >> .config
if ! grep -q "^CT_PREFIX_DIR=" .config; then
    echo 'CT_PREFIX_DIR="${RISCV}"' >> .config
fi
if ! grep -q "^CT_LOCAL_TARBALLS_DIR=" .config; then
    echo "CT_LOCAL_TARBALLS_DIR=\"$(pwd)/src"\" >> .config
fi
if [ -n "$CI" ]; then
    echo "CT_LOG_PROGRESS_BAR=n" >> .config
fi
$RISCV/bin/ct-ng upgradeconfig > /dev/null

# deduce tuple, sysroot
TUPLE=$($RISCV/bin/ct-ng -s show-tuple)
if ! case $TUPLE in riscv*) ;; *) false;; esac; then
    echo "Fatal error: build script can only build RISCV toolchains, request for $TUPLE was specified instead"
    exit 1
fi
SYSROOT=$RISCV/$TUPLE/sysroot

# check previous install and clear sysroot between builds if exists
if [ -x "$RISCV/bin/$TUPLE-gcc" ]; then
    echo "Warning: RISCV directory already seems to contain a toolchain for $TUPLE";
    read -p "Are you sure you want replace it (N/y)? " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        exit 1
    elif [ -d "$SYSROOT" ]; then
        chmod -R u+w $SYSROOT
        rm -rf $SYSROOT/*
    fi
fi

# FIXME: remove gnumake symlink to prevent build stuck
if grep -q "^CT_COMP_TOOLS_FOR_HOST=y" .config && grep -q "^CT_COMP_TOOLS_MAKE=y" .config; then
    # remove a symlink if it exists otherwise rebuild will break
    echo "Removing symlink to gnumake to prevent build failure..."
    set +e
    chmod -f u+w $RISCV/bin/
    chmod -f u+w $RISCV/bin/gnumake
    rm -f $RISCV/bin/gnumake
    chmod -f u-w $RISCV/bin/
    set -e
fi

# build the toolchain
echo "Starting toolchain build..."
unset LD_LIBRARY_PATH
$RISCV/bin/ct-ng build

if [ ! -d $SYSROOT ]; then
    SYSROOT=
else
    SYSROOT=$(readlink -f $SYSROOT)
fi

# fixup generic hardcoded paths in installed host toolchain
# FIXME: this should be done properly by crosstool-ng
if grep -q "^CT_COMP_TOOLS_FOR_HOST=y" .config; then
    echo "Fixing hardcoded paths pointing to build directory..."
    chmod -R u+w $RISCV
    builddir=$(readlink -f $(pwd)/.build)
    replacedir=$(readlink -f $RISCV)
    find $RISCV/bin -type f -exec sed -i "s|$builddir/tools/bin/||g" {} \;
    find $RISCV/bin -type f -exec sed -i "s|NM=\".*\"|NM=\"nm\"|g" {} \;
    find $RISCV/ -iname "*.la" -type f -exec sed -i "s|-L$builddir/.*/build/build-gdb-native/zlib ||" {} \;
    chmod -R u-w $RISCV
fi

# demultilib paths in riscv toolchain (needed for buildroot)
# FIXME: this should be done properly by crosstool-ng
if [ ! -z "$SYSROOT" ] && grep -q "^CT_DEMULTILIB=y" .config; then
    echo "Combining libraries into single directory..."
    libdir=
    if grep -q "^CT_ARCH_64=y" .config; then
        libdir=lib64
    elif grep -q "^CT_ARCH_32=y" .config; then
        libdir=lib32
    fi
    abidir=$(grep "^CT_ARCH_ABI" .config | sed "s/CT_ARCH_ABI=//" | sed -e 's/^"//' -e 's/"$//')
    multilibdir="$SYSROOT/$libdir/$abidir"
    if [ -z "$libdir" ] || [ -z "$abidir" ] || [ ! -d "$SYSROOT/$libdir/$abidir" ]; then
        echo "Fatal error: cannot find multilib directory to combine with lib"
        exit 1
    fi

    chmod -R u+w $SYSROOT
    ORIGDIR=$(pwd)
    for dir in $libdir/$abidir usr/$libdir/$abidir; do
        cd $SYSROOT/$dir
        curdir=$(readlink -f $(pwd))
        # move files to libdir, leaving symlink and create symlinks to symlinks
	      for file in $(find . -type f -o -type l); do
            if [ -e ../../lib/$file ]; then
                echo "Warning: cannot fixup library path, $file already exists in lib"
                continue
            fi
            path=$(readlink -f $file)
            reldir=$(dirname $file)
            mkdir -p ../../lib/$reldir
            if [ -L $file ]; then
                ln -s $path $curdir/../../lib/$file
            else
                mv $file $curdir/../../lib/$file
                ln -s $curdir/../../lib/$file $file
            fi
        done
    done

    for dir in lib usr/lib; do
        cd $SYSROOT/$dir
        # clean symlinks in libdir
        for file in $(find . -type l); do
            destrelsysroot=$(readlink -f $file | sed "s|$SYSROOT/||")
            reldir=$(dirname $file)
            srcrelsysroot=$(readlink -f $reldir | sed "s|$SYSROOT||")
            sysrootrel=$(printf '../%.0s' $(seq 1 $(echo $srcrelsysroot | tr -cd '/' | wc -c)))
            prevdir=$(pwd)
            cd $reldir
            ln -sf $sysrootrel$destrelsysroot $(basename $file)
            cd $prevdir
        done
    done

    # remove original lib directories
    rm -rf $SYSROOT/$libdir
    rm -rf $SYSROOT/usr/$libdir

    # create necessary symlinks to make the toolchain work
    for dir in . usr; do
        cd $SYSROOT/$dir
        ln -s lib $libdir
        cd lib
        ln -s . $abidir
    done

    cd $ORIGDIR
    chmod -R u-w $SYSROOT
fi

# alias the toolchain if requested ($2 = vendor alias, $3 = optional suffix useful for buildroot)
if [ ! -z "$2" ] || [ ! -z "$3" ]; then
    chmod -R u+w $RISCV/bin
    vendor=$(echo "$TUPLE" | sed -E 's/^\w*-(\w*)-.*/\1/')
    for tf in $RISCV/bin/$TUPLE*; do
        alias=$(echo "$tf" | sed -e "s/$vendor/$2/")
        ln -sf $(readlink -f $tf) $alias
        if [ ! -z "$3" ]; then
            ln -sf $(readlink -f $tf) $alias.$3
        fi
    done
    chmod -R u-w $RISCV/bin
fi
