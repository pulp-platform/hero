# find external prefix
prefix_var="BR2_TOOLCHAIN_EXTERNAL_PREFIX"
prefix_asn=$(make printvars VARS="$prefix_var" 2>/dev/null)
if [ $(echo $prefix_asn | wc -l) -ne 1 ]; then
    echo "Fatal error: the script does not seem to be ran from a buildroot directory"
    exit 0
fi

prefix=$(echo $prefix_asn | sed -E "s/^$prefix_var=(.*)/\1/")
prefix="${prefix%\"}"
prefix="${prefix#\"}"

# create sdk
echo "Creating SDK..."
make sdk
sdk=images/*_sdk-buildroot.tar.gz
sdk_name=$(basename $sdk)
sdk_name=${sdk_name%.tar.gz}
br_prefix=${sdk_name%_sdk-buildroot}

# check previous install and clear sysroot between builds if exists
if [ -d "$RISCV/$br_prefix" ]; then
    echo "Warning: RISCV directory already seems to contain a SDK for $br_prefix";
    read -p "Are you sure you want replace it (N/y)? " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        exit 1
    else
        chmod -R u+w $RISCV
        rm -rf $RISCV/$br_prefix
        chmod -R u-w $RISCV
    fi
fi

# loop through toolchain symlinks and temporarily remove some for sdk packaging
echo "Finding paths to exclude..."
echo -n > exclude_sdk.txt
for f in host/bin/$prefix*; do
    tf=$(echo $f | sed -e "s/^host/$sdk_name/")
    # do not include br_real files
    if [[ $f == *.br_real ]]; then
        echo $tf >> exclude_sdk.txt
    fi
    symlink=$(readlink $f)
    # do not include files not pointing to the toolchain-wrapper
    if [[ $symlink != "toolchain-wrapper" ]]; then
        echo $tf >> exclude_sdk.txt
    fi
done

# untar sdk with excluded paths at the installation location
echo "Installing SDK..."
chmod -R u+w $RISCV
tar -xzf $sdk --exclude-from exclude_sdk.txt --strip-components=1 -C $RISCV

# relocate the installed toolchain
$RISCV/relocate-sdk.sh
rm $RISCV/relocate-sdk.sh

# add symlink to buildroot sysroot
echo "Aliasing SDK sysroot to toolchain prefix..."
ln -sf $RISCV/$br_prefix $RISCV/$prefix

# finalize install
chmod -R u-w $RISCV
