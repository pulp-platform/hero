## INSTALL A SDK FROM A BUILDROOT ENVIRONMENT ##

if [ -z "$HERO_INSTALL" ]; then
  echo "Fatal error: set HERO_INSTALL to location to install the SDK"
  exit 1
fi

# stop on all errors
set -e

# find external prefix
prefix_var="BR2_TOOLCHAIN_EXTERNAL_PREFIX"
prefix_asn=$(make -s printvars VARS="$prefix_var" 2>/dev/null)
if [ $(echo $prefix_asn | wc -l) -ne 1 ]; then
    echo "Fatal error: the script does not seem to be ran from a buildroot directory"
    exit 1
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
if [ -d "$HERO_INSTALL/$br_prefix" ]; then
    echo "Warning: HERO_INSTALL directory already seems to contain a SDK for $br_prefix";
    read -p "Are you sure you want replace it (N/y)? " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        exit 1
    else
        chmod -R u+w ${HERO_INSTALL}
        rm -rf ${HERO_INSTALL}/$br_prefix
        chmod -R u-w ${HERO_INSTALL}
    fi
fi

# copy the toolchain wrapper to architecture specific location
cp host/bin/toolchain-wrapper host/bin/$prefix-toolchain-wrapper
echo "$sdk_name/bin/toolchain-wrapper" > exclude_sdk.txt

# loop through toolchain symlinks and temporarily remove some for sdk packaging
echo "Finding paths to exclude..."
echo "$sdk_name/lib64" >> exclude_sdk.txt
for f in host/bin/$prefix*; do
    # skip toolchain wrapper
    if [[ $f ==  *-toolchain-wrapper ]]; then
      continue
    fi
    tf=$(echo $f | sed -e "s/^host/$sdk_name/")
    # do not include br_real files
    if [[ $f == *.br_real ]]; then
        echo $tf >> exclude_sdk.txt
    fi
    symlink=$(readlink $f)
    if [[ $symlink != *toolchain-wrapper ]]; then
      # do not include files not pointing to the toolchain-wrapper
      echo $tf >> exclude_sdk.txt
    else
      # update the symlink to point to the architecture specific location
      ln -sf $prefix-toolchain-wrapper $f
    fi
done

# untar sdk with excluded paths at the installation location
echo "Installing SDK..."
chmod -R u+w ${HERO_INSTALL}
tar -xzf $sdk --exclude-from exclude_sdk.txt --strip-components=1 -C $HERO_INSTALL

# relocate the installed toolchain
${HERO_INSTALL}/relocate-sdk.sh
rm ${HERO_INSTALL}/relocate-sdk.sh

# add symlink to buildroot sysroot
echo "Aliasing SDK sysroot to toolchain prefix..."
if [ -d "$HERO_INSTALL/$br_prefix/sysroot" ]; then
    ln -sf $br_prefix/sysroot ${HERO_INSTALL}/$prefix
else
    ln -sf $br_prefix ${HERO_INSTALL}/$prefix
fi

# finalize install
chmod -R u-w ${HERO_INSTALL}
