#!/usr/bin/env bash

set -e

if [ -z "$VIVADO" ]; then
  VIVADO="vivado-2017.2"
fi
readonly VIVADO
readonly TARGET=zcu102


menuconfig() {
  echo "\

In the following menuconfig, $1

Finally, save and exit menuconfig.

Hit any button when you are ready."
  read -n 1
  shift 1
  $VIVADO petalinux-config $@
}

$VIVADO petalinux-create -t project -n "$TARGET" --template zynqMP
cd "$TARGET"

$VIVADO petalinux-config \
  --get-hw-description "../../hardware/fpga/hero_exil$TARGET/hero_exil$TARGET.sdk"

mkdir -p components/ext_sources
cd components/ext_sources
git clone git://github.com/Xilinx/linux-xlnx.git
cd linux-xlnx
git checkout tags/xilinx-v2017.2

cd ../../..
menuconfig "\
go to 'Linux Components Selection --->'
'linux-kernel' and select 'ext-local-src'. Then select 'External linux-kernel
local source settings --->' and enter

    \${TOPDIR}/../components/ext_sources/linux-xlnx

for 'External linux-kernel local source path'."

menuconfig "\
go to 'General Setup --->' and enter

    -xilinx-v2017.2

for 'Local version - append to kernel release'." -c kernel

$VIVADO petalinux-build

$VIVADO petalinux-package --image

cp "../../hardware/fpga/hero_exil$TARGET/hero_exil${TARGET}.runs/impl_1/hero_exil${TARGET}_wrapper.bit" \
  images/linux/
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
