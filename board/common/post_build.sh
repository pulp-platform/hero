echo "Adding required symlinks to library directories"
# FIXME: those symlinks should be copied by buildroot from the toolchain
abidir=$(find $1/lib -iname 'ld-linux-*' | sed -e "s|.*/ld-linux-||" -e "s|.so.*||" | cut -d '-' -f 2)
ln -s . $1/usr/lib/$abidir
ln -s . $1/lib/$abidir

echo "Removing NFS init.d script"
rm -f $1/etc/init.d/S60nfs

echo "Generating random seed from host"
dd if=/dev/urandom of=$1/etc/random-seed count=512
