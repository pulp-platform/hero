#!/usr/bin/env bash
THIS_DIR=$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")

set -e

if [ -z "$VIVADO" ]; then
  VIVADO="vivado-2017.2"
fi
readonly VIVADO
readonly TARGET=zcu102

cd `pwd -P`

if [ ! -d "$TARGET" ]; then
    $VIVADO petalinux-create -t project -n "$TARGET" --template zynqMP
fi
cd "$TARGET"

$VIVADO petalinux-config --oldconfig --get-hw-description "../../hardware/fpga/hero_exil$TARGET/hero_exil$TARGET.sdk"

mkdir -p components/ext_sources
cd components/ext_sources
if [ ! -d "linux-xlnx" ]; then
    git clone --single-branch --branch xilinx-v2017.2 git://github.com/Xilinx/linux-xlnx.git
fi
cd linux-xlnx
git checkout tags/xilinx-v2017.2

cd ../../../
sed -i 's|CONFIG_SUBSYSTEM_COMPONENT_LINUX__KERNEL_NAME_LINUX__XLNX||' project-spec/configs/config
sed -i 's|CONFIG_SUBSYSTEM_ROOTFS_INITRAMFS||' project-spec/configs/config
echo 'CONFIG_SUBSYSTEM_ROOTFS_SD=y' >> project-spec/configs/config
echo 'CONFIG_SUBSYSTEM_COMPONENT_LINUX__KERNEL_NAME_EXT__LOCAL__SRC=y' >> project-spec/configs/config
echo 'CONFIG_SUBSYSTEM_COMPONENT_LINUX__KERNEL_NAME_EXT_LOCAL_SRC_PATH="${TOPDIR}/../../components/ext_sources/linux-xlnx"' >> project-spec/configs/config
echo 'CONFIG_SUBSYSTEM_SDROOT_DEV="/dev/mmcblk0p2"' >> project-spec/configs/config
echo 'CONFIG_SUBSYSTEM_MACHINE_NAME="zcu102-revb"' >> project-spec/configs/config

if [ -f $THIS_DIR/../local.cfg ] && grep -q PT_ETH_MAC $THIS_DIR/../local.cfg; then
    sed -e 's/PT_ETH_MAC/CONFIG_SUBSYSTEM_ETHERNET_PSU_ETHERNET_3_MAC/' $THIS_DIR/../local.cfg >> project-spec/configs/config
fi

$VIVADO petalinux-config --oldconfig --get-hw-description "../../hardware/fpga/hero_exil$TARGET/hero_exil$TARGET.sdk"

echo "
/include/ \"system-conf.dtsi\"
/include/ \"${THIS_DIR}/../board/xilzcu102/hero.dtsi\"
/ {
};
" > project-spec/meta-user/recipes-bsp/device-tree/files/system-user.dtsi

set +e
$VIVADO petalinux-build
echo "First build might fail, this is expected..."
set -e
mkdir -p build/tmp/work/aarch64-xilinx-linux/external-hdf/1.0-r0/git/plnx_aarch64/
cp project-spec/hw-description/system.hdf build/tmp/work/aarch64-xilinx-linux/external-hdf/1.0-r0/git/plnx_aarch64/
$VIVADO petalinux-build

$VIVADO petalinux-package --image

mkdir -p build/tmp/work/aarch64-xilinx-linux/external-hdf/1.0-r0/git/plnx_aarch64/

cp "../../hardware/fpga/hero_exil$TARGET/hero_exil${TARGET}.runs/impl_1/hero_exil${TARGET}_wrapper.bit" images/linux/
cd images/linux
if [ ! -f regs.init ]; then
  echo ".set. 0xFF41A040 = 0x3;" > regs.init
fi
echo "
the_ROM_image:
{
  [init] regs.init
  [fsbl_config] a53_x64
  [bootloader] zynqmp_fsbl.elf
  [pmufw_image] pmufw.elf
  [destination_device=pl] hero_exil${TARGET}_wrapper.bit
  [destination_cpu=a53-0, exception_level=el-3, trustzone] bl31.elf
  [destination_cpu=a53-0, exception_level=el-2] u-boot.elf
}
" > bootgen.bif

vivado-2017.2 petalinux-package --boot --force \
  --fsbl zynqmp_fsbl.elf \
  --fpga hero_exil${TARGET}_wrapper.bit \
  --u-boot u-boot.elf \
  --pmufw pmufw.elf \
  --bif bootgen.bif
