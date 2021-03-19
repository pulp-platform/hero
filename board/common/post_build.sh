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

echo "Setup Networking ${BR2_CONFIG}"
IP_ADDR=$(grep BR2_HERO_ETH_IP_ADDR ${BR2_CONFIG} | sed -e 's/.*=//' -e 's/^"//' -e 's/"$//')
if [ ! -z "$IP_ADDR" ]; then
  IP_NETMASK=$(grep BR2_HERO_ETH_NETMASK ${BR2_CONFIG} | sed -e 's/.*=//' -e 's/^"//' -e 's/"$//')
  IP_GATEWAY=$(grep BR2_HERO_ETH_GATEWAY ${BR2_CONFIG} | sed -e 's/.*=//' -e 's/^"//' -e 's/"$//')
  IP_DNS=$(grep BR2_HERO_ETH_DNS ${BR2_CONFIG} | sed -e 's/.*=//' -e 's/^"//' -e 's/"$//')

  echo "  IP........$IP_ADDR"
  echo "  Netmask...$IP_NETMASK"
  echo "  Gateway...$IP_GATEWAY"
  echo "  DNS.......$IP_DNS"

  rm -rf ${TARGET_DIR}/etc/network/interfaces
  echo "
# configure eth0 with static IP
auto lo
iface lo inet loopback

auto eth0
iface eth0 inet static
address $IP_ADDR
netmask $IP_NETMASK
gateway $IP_GATEWAY
pre-up /etc/network/nfs_check
wait-delay 15
hostname $(hostname)

" > ${TARGET_DIR}/etc/network/interfaces

  rm -rf ${TARGET_DIR}/etc/resolv.conf
  echo "nameserver $IP_DNS" > ${TARGET_DIR}/etc/resolv.conf

else
  echo "  IP........DHCP"
fi

