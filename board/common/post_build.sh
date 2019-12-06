echo "Removing NFS init.d script"
rm -f $1/etc/init.d/S60nfs

echo "Installing custom mount script"
EXT_MOUNT=$(grep BR2_HERO_EXT_MOUNT ${BR2_CONFIG} | sed -e 's/.*=//' -e 's/^"//' -e 's/"$//')
echo $EXTMOUNT
if [ -z "$EXT_MOUNT" ]; then
  rm $1/etc/init.d/S99extroot
else
  sed -i "s|EXTERNAL_MOUNT_POINT|${EXT_MOUNT}|" $1/etc/init.d/S99extroot
fi
