#!/usr/bin/env bash
THIS_DIR=$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")

set -e

# Initialize Python environment suitable for PetaLinux.
python3.6 -m venv .venv
ln -sf python3.6 .venv/bin/python3
source .venv/bin/activate

if [ -n "$NO_IIS" ]; then
  PETALINUX_VER=''
else
  if [ -z "$PETALINUX_VER" ]; then
    PETALINUX_VER="vitis-2019.2"
  fi
fi
readonly PETALINUX_VER
readonly TARGET=zcu102

cd `pwd -P`

# create project
if [ ! -d "$TARGET" ]; then
    $PETALINUX_VER petalinux-create -t project -n "$TARGET" --template zynqMP
fi
cd "$TARGET"

# initialize and set necessary configuration from config and local config
$PETALINUX_VER petalinux-config --oldconfig --get-hw-description "../../hardware/fpga/hero_exil$TARGET/hero_exil$TARGET.sdk"

mkdir -p components/ext_sources
cd components/ext_sources
if [ ! -d "linux-xlnx" ]; then
    git clone --single-branch --branch xilinx-v2019.2.01 git://github.com/Xilinx/linux-xlnx.git
fi
cd linux-xlnx
git checkout tags/xilinx-v2019.2.01

cd ../../../
sed -i 's|CONFIG_SUBSYSTEM_COMPONENT_LINUX__KERNEL_NAME_LINUX__XLNX||' project-spec/configs/config
sed -i 's|CONFIG_SUBSYSTEM_ROOTFS_INITRAMFS||' project-spec/configs/config
echo 'CONFIG_SUBSYSTEM_ROOTFS_SD=y' >> project-spec/configs/config
echo 'CONFIG_SUBSYSTEM_COMPONENT_LINUX__KERNEL_NAME_EXT__LOCAL__SRC=y' >> project-spec/configs/config
echo 'CONFIG_SUBSYSTEM_COMPONENT_LINUX__KERNEL_NAME_EXT_LOCAL_SRC_PATH="${TOPDIR}/../components/ext_sources/linux-xlnx"' >> project-spec/configs/config
echo 'CONFIG_SUBSYSTEM_SDROOT_DEV="/dev/mmcblk0p2"' >> project-spec/configs/config
echo 'CONFIG_SUBSYSTEM_MACHINE_NAME="zcu102-revb"' >> project-spec/configs/config

if [ -f $THIS_DIR/../local.cfg ] && grep -q PT_ETH_MAC $THIS_DIR/../local.cfg; then
    sed -e 's/PT_ETH_MAC/CONFIG_SUBSYSTEM_ETHERNET_PSU_ETHERNET_3_MAC/;t;d' $THIS_DIR/../local.cfg >> project-spec/configs/config
fi

$PETALINUX_VER petalinux-config --oldconfig --get-hw-description "../../hardware/fpga/hero_exil$TARGET/hero_exil$TARGET.sdk"

echo "
/include/ \"system-conf.dtsi\"
/include/ \"${THIS_DIR}/../board/xilzcu102/hero.dtsi\"
/ {
};
" > project-spec/meta-user/recipes-bsp/device-tree/files/system-user.dtsi

# start build
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

# add bitstream from local config
if [ -f $THIS_DIR/../local.cfg ] && grep -q HERO_BITSTREAM $THIS_DIR/../local.cfg; then
  bitstream=$(eval echo $(sed -e 's/BR2_HERO_BITSTREAM=//;t;d' $THIS_DIR/../local.cfg | tr -d '"'))
  cp $bitstream hero_exil${TARGET}_wrapper.bit
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
else
  echo "
the_ROM_image:
{
  [init] regs.init
  [bootloader] zynqmp_fsbl.elf
  [pmufw_image] pmufw.elf
  [destination_cpu=a53-0, exception_level=el-3, trustzone] bl31.elf
  [destination_cpu=a53-0, exception_level=el-2] u-boot.elf
}
" > bootgen.bif

  $PETALINUX_VER petalinux-package --boot --force \
    --fsbl zynqmp_fsbl.elf \
    --u-boot u-boot.elf \
    --pmufw pmufw.elf \
    --bif bootgen.bif
fi
