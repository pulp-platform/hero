#!/usr/bin/env bash

THIS_DIR=$(dirname "$(readlink -f "$0")")

### BUILDS A TOOLCHAIN USING CROSSTOOL-NG ###

# stop on errors
set -e

# configuration
CROSSTOOL_VERSION=1.25.0
HELP2MAN_VERSION=1.47.10
TEXINFO_VERSION=6.6

echo "Using PYTHON=$PYTHON"

if [ "$#" -lt 1 ] || [ ! -f "$1" ]; then
    echo "Fatal error: expects at least a single argument with crosstool config"
    exit 1
fi
if [ -z "$HERO_INSTALL" ]; then
    echo "Fatal error: set HERO_INSTALL to install location of the toolchain"
    exit 1
fi

conf_dir=$(readlink -f $(dirname "$1"))

# FIXME: install dependencies for crosstool-ng if not found on host
# help2man might be missing, install it temporary if it is missing
export PATH=$PATH:$(pwd)/install/bin/
if ! command -v help2man >/dev/null 2>&1; then
    echo "Not having help2man, installing a temporary version for crosstool..."
    curl https://ftp.gnu.org/gnu/help2man/help2man-$HELP2MAN_VERSION.tar.xz | tar -xJp
    cd help2man-$HELP2MAN_VERSION/
    ./configure --prefix=$HERO_INSTALL
    make -j$(nproc)
    make install
    cd ..
fi
# makeinfo might be missing, install it temporary if it is missing
if ! command -v makeinfo >/dev/null 2>&1; then
    echo "Not having texinfo, installing a temporary version for crosstool..."
    curl https://ftp.gnu.org/gnu/texinfo/texinfo-$TEXINFO_VERSION.tar.xz | tar -xJp
    cd texinfo-$TEXINFO_VERSION/
    ./configure --prefix=$HERO_INSTALL
    make -j$(nproc)
    make install
    cd ..
fi

mkdir -p $HERO_INSTALL
# download and install crosstool-ng
if [ ! -x "$HERO_INSTALL/bin/ct-ng" ]; then
    chmod -R u+w $HERO_INSTALL
    echo "No crosstool-ng found, installing..."
    curl https://codeload.github.com/crosstool-ng/crosstool-ng/tar.gz/crosstool-ng-$CROSSTOOL_VERSION | tar -xzp
    cd crosstool-ng-crosstool-ng-$CROSSTOOL_VERSION
    # FIXME removed patches for 1.25
    for f in $conf_dir/patches/crosstool-ng/*.patch; do
        patch -p1 < $f
    done
    ./bootstrap
    ./configure --prefix=$HERO_INSTALL
    if [ ! $? -eq 0 ]; then
        echo "Fatal error: failed to configure crosstool-ng"
	      exit
    fi
    cd ..
    make -C crosstool-ng-crosstool-ng-$CROSSTOOL_VERSION
    make -C crosstool-ng-crosstool-ng-$CROSSTOOL_VERSION install
fi

# symlink the local patches directory in the configs to be used during build
# FIXME: currently only hardcoded patches directory will be used
if [ ! -L "patches" ]; then
    echo "Symlinking patches directory to build directory"
    ln -s $conf_dir/patches $(pwd)/patches
fi

# initialize the configuration
echo "Initializing toolchain build..."
cp "$1" .config
mkdir -p src
echo >> .config
if ! grep -q "^CT_PREFIX_DIR=" .config; then
    echo 'CT_PREFIX_DIR="${HERO_INSTALL}"' >> .config
fi
if ! grep -q "^CT_LOCAL_TARBALLS_DIR=" .config; then
    echo "CT_LOCAL_TARBALLS_DIR=\"$(pwd)/src"\" >> .config
fi
if [ -n "$CI" ]; then
    echo "CT_LOG_PROGRESS_BAR=n" >> .config
fi
$HERO_INSTALL/bin/ct-ng upgradeconfig > /dev/null

# # deduce tuple, sysroot
TUPLE=$($HERO_INSTALL/bin/ct-ng -s show-tuple)
echo "Tuple found : ${TUPLE}"
if [ -z "$TUPLE" ]; then
    echo "Failed to get tuple for config $1!"
    exit 1
fi
ARCH=$(echo $TUPLE | cut -f1 -d'-')
if [ -z "$ARCH" ]; then
    echo "Failed to deduce architecture from tuple $TUPLE with config $1!"
    exit 1
fi
echo "Arch found : ${ARCH}"
SYSROOT=$HERO_INSTALL/$TUPLE/sysroot

# check previous install and clear sysroot between builds if exists
if [ -x "$HERO_INSTALL/bin/$TUPLE-gcc" ]; then
    echo "Warning: HERO_INSTALL directory already seems to contain a toolchain for $TUPLE";
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
    chmod -f u+w $HERO_INSTALL/bin/
    chmod -f u+w $HERO_INSTALL/bin/gnumake
    rm -f $HERO_INSTALL/bin/gnumake
    chmod -f u-w $HERO_INSTALL/bin/
    set -e
fi

# build the toolchain
echo "Starting toolchain build..."
unset LD_LIBRARY_PATH
$HERO_INSTALL/bin/ct-ng build

if [ ! -d $SYSROOT ]; then
    SYSROOT=
else
    SYSROOT=$(readlink -f $SYSROOT)
fi

# fixup generic hardcoded paths in installed host toolchain
# FIXME: this should be done properly by crosstool-ng
if grep -q "^CT_COMP_TOOLS_FOR_HOST=y" .config; then
    echo "Fixing hardcoded paths pointing to build directory..."
    chmod -R u+w $HERO_INSTALL
    builddir=$(readlink -f $(pwd)/.build)
    replacedir=$(readlink -f $HERO_INSTALL)
    find $HERO_INSTALL/bin -type f -exec sed -i "s|$builddir/tools/bin/||g" {} \;
    find $HERO_INSTALL/bin -type f -exec sed -i "s|NM=\".*\"|NM=\"nm\"|g" {} \;
    find $HERO_INSTALL/ -iname "*.la" -type f -exec sed -i "s|-L$builddir/.*/build/build-gdb-native/zlib ||" {} \;
    chmod -R u-w $HERO_INSTALL
fi

# demultilib paths in riscv toolchain (needed for buildroot)
# FIXME: this should be done properly by crosstool-ng
if case $ARCH in riscv*) ;; *) false;; esac; then
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
                    # Keep symlink where it is and link to it from `../../lib`.
                    linkfile="../../lib/$file"
                    target="../$libdir/$abidir/$file"
                else
                    # Move regular file to `../../lib` and link to that.
                    linkfile="$file"
                    target="../../lib/$file"
                    mv "$file" "$target"
                fi
                ln -s "$target" "$linkfile"
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
fi

# alias the toolchain if requested ($2 = vendor alias, $3 = optional suffix useful for buildroot)
# FIXME !!!!
if [ ! -z "$2" ] || [ ! -z "$3" ]; then
    chmod -R u+w $HERO_INSTALL/bin
    vendor=$(echo "$TUPLE" | sed -E 's/^\w*-(\w*)-.*/\1/')
    cd "$HERO_INSTALL/bin"
    for tf in $TUPLE*; do
        alias=$(echo "$tf" | sed -e "s/$vendor/$2/")
        echo "tuple=$TUPLE vendor=$vendor alias=$alias"
        echo "ln -sf $tf $alias"
        ln -sf $tf $alias
        if [ ! -z "$3" ]; then
            echo "ln -sf $tf $alias.$3"
            ln -sf $tf $alias.$3
            echo "ln -sf $tf $tf.$3"
            ln -sf $tf $tf.$3
        fi
    done
    cd - > /dev/null
    chmod -R u-w $HERO_INSTALL/bin
fi
