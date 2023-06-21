#!/usr/bin/env bash
readonly THIS_DIR=$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")
readonly HERO_ROOT="$(readlink -f "$THIS_DIR/..")"
readonly LOCAL_CFG="$HERO_ROOT/local.cfg"

set -e

# Change working directory to path of script, so this script can be executed from anywhere.
cd "$THIS_DIR"
# Resolve symlinks.
cd "$(pwd -P)"

# Obtain bitstream path from configuration.
set +e
bitstream="$("$HERO_ROOT/util/configfile/get_value" -s "$LOCAL_CFG" BR2_HERO_BITSTREAM \
    | tr -d '"')";
if test "$?" -ne 0; then
  >&2 echo "Error: '$1' is not defined in '$LOCAL_CFG'!"
  exit 1
fi
set -e
readonly bitstream="${bitstream//\$BR2_EXTERNAL_HERO_PATH/$HERO_ROOT}"
if ! test -r "$bitstream"; then
  echo "Error: Path to bitstream ('$bitstream') is not readable!"
  exit 1
fi

# Initialize Python environment suitable for PetaLinux.
python3.6 -m venv .venv
ln -sf python3.6 .venv/bin/python3
source .venv/bin/activate

# Read Petalinux name
if [ -n "$NO_IIS" ]; then
  PETALINUX_VER=''
else
  if [ -z "$PETALINUX_VER" ]; then
    PETALINUX_VER="vitis-2019.2"
  fi
fi
readonly PETALINUX_VER
readonly TARGET=zcu102

# create project
if [ ! -d "$TARGET" ]; then
    $PETALINUX_VER petalinux-create -t project -n "$TARGET" --template zynqMP
fi
cd "$TARGET"

# initialize and set necessary configuration from config and local config
$PETALINUX_VER petalinux-config --oldconfig --get-hw-description "$HERO_ROOT/hardware/fpga/hero_exil$TARGET/hero_exil$TARGET.sdk"

mkdir -p components/ext_sources
cd components/ext_sources
if [ ! -d "linux-xlnx" ]; then
    git clone --depth 1 --single-branch --branch xilinx-v2019.2.01 https://github.com/Xilinx/linux-xlnx.git
fi
cd linux-xlnx
git checkout tags/xilinx-v2019.2.01

cd ../../../
sed -i 's|CONFIG_SUBSYSTEM_COMPONENT_LINUX__KERNEL_NAME_LINUX__XLNX.*||' project-spec/configs/config
echo 'CONFIG_SUBSYSTEM_COMPONENT_LINUX__KERNEL_NAME_EXT__LOCAL__SRC=y' >> project-spec/configs/config
echo 'CONFIG_SUBSYSTEM_COMPONENT_LINUX__KERNEL_NAME_EXT_LOCAL_SRC_PATH="${TOPDIR}/../components/ext_sources/linux-xlnx"' >> project-spec/configs/config
sed -i 's|CONFIG_SUBSYSTEM_MACHINE_NAME.*||' project-spec/configs/config
echo 'CONFIG_SUBSYSTEM_MACHINE_NAME="zcu102-revb"' >> project-spec/configs/config

# Cleanup All RootFS Options
sed -i 's|CONFIG_SUBSYSTEM_ROOTFS_INITRAMFS.*||' project-spec/configs/config
sed -i 's|CONFIG_SUBSYSTEM_ROOTFS_INITRD.*||' project-spec/configs/config
sed -i 's|CONFIG_SUBSYSTEM_ROOTFS_JFFS2.*||' project-spec/configs/config
sed -i 's|CONFIG_SUBSYSTEM_ROOTFS_JFFS2.*||' project-spec/configs/config
sed -i 's|CONFIG_SUBSYSTEM_ROOTFS_NFS.*||' project-spec/configs/config
sed -i 's|CONFIG_SUBSYSTEM_ROOTFS_OTHER.*||' project-spec/configs/config

# Select RootFS Option (Default: SD_CARD)
nfsrootfs="$("$HERO_ROOT/util/configfile/get_value" -s "$LOCAL_CFG" PT_ROOTFS_NFS \
    | tr -d '"')";
if ! [[ $nfsrootfs == "y" ]]; then
  # SD-CARD
  echo 'CONFIG_SUBSYSTEM_ROOTFS_SD=y' >> project-spec/configs/config
  echo 'CONFIG_SUBSYSTEM_SDROOT_DEV="/dev/mmcblk0p2"' >> project-spec/configs/config
else
  # NFS ROOTFS
  nfsrootdir="$("$HERO_ROOT/util/configfile/get_value" -s "$LOCAL_CFG" PT_NFSROOT_DIR)";
  if [ -z $nfsrootdir ]; then
    >&2 echo "Error: PT_NFSROOT_DIR is not defined in '$LOCAL_CFG'!"
    exit 1
  fi
  nfsserverip="$("$HERO_ROOT/util/configfile/get_value" -s "$LOCAL_CFG" PT_NFSSERVER_IP \
    | tr -d '"')";
  if [ -z $nfsserverip ]; then
    >&2 echo "Error: PT_NFSSERVER_IP is not defined in '$LOCAL_CFG'!"
    exit 1
  fi
  set -e
  echo "CONFIG_SUBSYSTEM_ROOTFS_NFS=$nfsrootfs" >> project-spec/configs/config
  echo "CONFIG_SUBSYSTEM_NFSROOT_DIR=$nfsrootdir" >> project-spec/configs/config
  echo "CONFIG_SUBSYSTEM_NFSSERVER_IP=$nfsserverip" >> project-spec/configs/config
fi

# Ethernet Settings

# Set MAC address if specified
sed -i 's|CONFIG_SUBSYSTEM_ETHERNET_PSU_ETHERNET_3_MAC.*||' project-spec/configs/config
eth_mac="$("$HERO_ROOT/util/configfile/get_value" -s "$LOCAL_CFG" PT_ETH_MAC \
    | tr -d '"')";
if ! [ -n $eth_mac ]; then
    echo "CONFIG_SUBSYSTEM_ETHERNET_PSU_ETHERNET_3_MAC=$eth_mac" >> project-spec/configs/config
else
    echo "CONFIG_SUBSYSTEM_ETHERNET_PSU_ETHERNET_3_MAC=\"ff:ff:ff:ff:ff:ff\"" >> project-spec/configs/config
fi

# Set IP Configuration
sed -i 's|CONFIG_SUBSYSTEM_ETHERNET_PSU_ETHERNET_3_USE_DHCP=y||' project-spec/configs/config
ip="$("$HERO_ROOT/util/configfile/get_value" -s "$LOCAL_CFG" BR2_HERO_ETH_IP_ADDR \
    | tr -d '"')";
if [ -z $ip ]; then
  # DHCP
  echo 'CONFIG_SUBSYSTEM_ETHERNET_PSU_ETHERNET_3_USE_DHCP=y' >> project-spec/configs/config
else
  # Static IP Configuration
  echo '# CONFIG_SUBSYSTEM_ETHERNET_PSU_ETHERNET_3_USE_DHCP is not set' >> project-spec/configs/config
  set +e
  netmask="$("$HERO_ROOT/util/configfile/get_value" -s "$LOCAL_CFG" BR2_HERO_ETH_NETMASK \
    | tr -d '"')";
  if [ -z $netmask ]; then
    >&2 echo "Error: BR2_HERO_ETH_NETMASK is not defined in '$LOCAL_CFG'!"
    exit 1
  fi
  gateway="$("$HERO_ROOT/util/configfile/get_value" -s "$LOCAL_CFG" BR2_HERO_ETH_GATEWAY \
    | tr -d '"')";
  if [ -z $gateway ]; then
    >&2 echo "Error: BR2_HERO_ETH_GATEWAY is not defined in '$LOCAL_CFG'!"
    exit 1
  fi
  set -e
  echo "CONFIG_SUBSYSTEM_ETHERNET_PSU_ETHERNET_3_IP_ADDRESS=$ip" >> project-spec/configs/config
  echo "CONFIG_SUBSYSTEM_ETHERNET_PSU_ETHERNET_3_IP_NETMASK=$netmask" >> project-spec/configs/config
  echo "CONFIG_SUBSYSTEM_ETHERNET_PSU_ETHERNET_3_IP_GATEWAY=$gateway" >> project-spec/configs/config
fi

echo "
/include/ \"system-conf.dtsi\"
/include/ \"${HERO_ROOT}/board/xilzcu102/hero.dtsi\"
/ {
};
" > project-spec/meta-user/recipes-bsp/device-tree/files/system-user.dtsi

# Configure RootFS
rootfs_enable() {
    sed -i -e "s/# CONFIG_$1 is not set/CONFIG_$1=y/" project-spec/configs/rootfs_config
}
for pkg in \
    bash \
    bash-completion \
    bc \
    ed \
    grep \
    patch \
    sed \
    util-linux \
    util-linux-blkid \
    util-linux-lscpu \
    vim \
; do
  rootfs_enable $pkg
done

create_install_app() {
    $PETALINUX_VER petalinux-create --force -t apps --template install -n $1 --enable
    cd project-spec/meta-user/recipes-apps/$1
    patch <"$THIS_DIR/recipes-apps/$1/${1}.bb.patch"
    rm -r files
    cp -r "$THIS_DIR/recipes-apps/$1/files" .
    cd ->/dev/null
}
# Create application that will mount SD card folders on boot.
create_install_app init-mount
# Create application that will execute scripts from SD card on boot.
create_install_app init-exec-scripts
# Create application to deploy custom `/etc/sysctl.conf`.
cp "$HERO_ROOT/board/common/overlay/etc/sysctl.conf" "$THIS_DIR/recipes-apps/sysctl-conf/files/"
create_install_app sysctl-conf

# Build PetaLinux.
set +e
$PETALINUX_VER petalinux-build
echo "First build might fail, this is expected..."
set -e
mkdir -p build/tmp/work/aarch64-xilinx-linux/external-hdf/1.0-r0/git/plnx_aarch64/
cp project-spec/hw-description/system.hdf build/tmp/work/aarch64-xilinx-linux/external-hdf/1.0-r0/git/plnx_aarch64/
$PETALINUX_VER petalinux-build

mkdir -p build/tmp/work/aarch64-xilinx-linux/external-hdf/1.0-r0/git/plnx_aarch64/

cd images/linux
if [ ! -f regs.init ]; then
  echo ".set. 0xFF41A040 = 0x3;" > regs.init
fi

# Generate images including bitstream with `petalinux-package`.
cp "$bitstream" hero_exil${TARGET}_wrapper.bit
echo "
the_ROM_image:
{
  [init] regs.init
  [bootloader] zynqmp_fsbl.elf
  [pmufw_image] pmufw.elf
  [destination_device=pl] hero_exil${TARGET}_wrapper.bit
  [destination_cpu=a53-0, exception_level=el-3, trustzone] bl31.elf
  [destination_cpu=a53-0, exception_level=el-2] u-boot.elf
}
" > bootgen.bif
$PETALINUX_VER petalinux-package --boot --force \
  --fsbl zynqmp_fsbl.elf \
  --fpga hero_exil${TARGET}_wrapper.bit \
  --u-boot u-boot.elf \
  --pmufw pmufw.elf \
  --bif bootgen.bif
