#!/usr/bin/env bash

echo "Removing NFS init.d script"
rm -f $1/etc/init.d/S60nfs

echo "Installing optional custom mount script"
EXT_MOUNT=$(grep BR2_HERO_EXT_MOUNT ${BR2_CONFIG} | sed -e 's/.*=//' -e 's/^"//' -e 's/"$//')
if [ -z "$EXT_MOUNT" ]; then
  rm $1/etc/init.d/S99extroot
else
  sed -i "s|EXTERNAL_MOUNT_POINT|${EXT_MOUNT}|" $1/etc/init.d/S99extroot
fi

echo "Installing optional authorized key files"
AUTH_KEYS=$(grep BR2_HERO_AUTHORIZED_KEYS ${BR2_CONFIG} | sed -e 's/.*=//' -e 's/^"//' -e 's/"$//')
if [ ! -z "$AUTH_KEYS" ]; then
  mkdir -p ${TARGET_DIR}/root/.ssh/
  cp $AUTH_KEYS ${TARGET_DIR}/root/.ssh/authorized_keys
fi
