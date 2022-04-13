#!/usr/bin/env bash

# set system from hero device tree
#ln -sf hero.dtb ${BINARIES_DIR}/system.dtb

# Remove Buildroot's host binaries from the path used by PetaLinux, because those binaries can cause
# problems with PetaLinux.
readonly PATH_FOR_PETALINUX=$(echo $PATH \
    | tr ':' '\n' \
    | grep -E -v "^$BR2_EXTERNAL_HERO_PATH/output/br-har-exilzcu102/host/s?bin$" \
    | perl -pe 'chomp if eof' \
    | tr '\n' ':')

# build the petalinux zcu102 config
cd ${BR2_EXTERNAL_HERO_PATH}/petalinux/
env PATH=$PATH_FOR_PETALINUX ./zcu102.sh
cp ${BR2_EXTERNAL_HERO_PATH}/petalinux/zcu102/images/linux/{bl31.bin,bl31.elf,image.ub,Image,pmufw.elf,regs.init,system.dtb,System.map.linux,u-boot.bin,zynqmp_fsbl.elf} $1
cp ${BR2_EXTERNAL_HERO_PATH}/petalinux/zcu102/images/linux/BOOT.BIN $1/boot.bin
cd -

support/scripts/genimage.sh -c ${BR2_EXTERNAL_HERO_PATH}/board/xilzcu102/genimage.cfg
