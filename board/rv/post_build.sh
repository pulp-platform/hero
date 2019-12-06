echo "Adding required symlinks to library directories"
# FIXME: those symlinks should be copied by buildroot from the toolchain
abidir=$(find $1/lib -iname 'ld-linux-*' | sed -e "s|.*/ld-linux-||" -e "s|.so.*||" | cut -d '-' -f 2)
ln -s . $1/usr/lib/$abidir >/dev/null 2>&1 || true
ln -s . $1/lib/$abidir >/dev/null 2>&1 || true
