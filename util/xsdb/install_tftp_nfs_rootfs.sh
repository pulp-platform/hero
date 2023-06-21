#!/usr/bin/env bash
THIS_DIR=$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")

CONFIG_FILE=$THIS_DIR/../../local.cfg
OUTPUT_DIR=$THIS_DIR/../../output

if [ -f ${CONFIG_FILE} ] && grep -q PT_TFTPBOOT_DIR ${CONFIG_FILE}; then
    eval TFTPBOOT_DIR=$(grep PT_TFTPBOOT_DIR ${CONFIG_FILE} | sed 's/.*=//' | tr -d '"')
    echo "Installing Boot Files: ${OUTPUT_DIR}/br-har-exilzcu102/images/ -> $TFTPBOOT_DIR"
    cp ${OUTPUT_DIR}/br-har-exilzcu102/images/Image $TFTPBOOT_DIR
    cp ${OUTPUT_DIR}/br-har-exilzcu102/images/system.dtb $TFTPBOOT_DIR
else
    echo "Installing Boot Files: SKIPPED (PT_TFTPBOOT_DIR is not set in local.cfg)"
fi

if [ -f ${CONFIG_FILE} ] && grep -q PT_NFSROOT_DIR ${CONFIG_FILE}; then
    eval NFSROOT_DIR=$(grep PT_NFSROOT_DIR ${CONFIG_FILE} | sed 's/.*=//' | tr -d '"')
    echo "Installing Host RootFS: ${OUTPUT_DIR}/br-har-exilzcu102/images/rootfs.tar -> $NFSROOT_DIR"
    tar -xf ${OUTPUT_DIR}/br-har-exilzcu102/images/rootfs.tar -C $NFSROOT_DIR
    echo "Installing HERO RootFS: ${OUTPUT_DIR}/har-rootfs.tar -> $NFSROOT_DIR/mnt"
    tar -xf ${OUTPUT_DIR}/har-rootfs.tar -C $NFSROOT_DIR/mnt
else
    echo "Installing RootFS: SKIPPED (PT_NFSROOT_DIR is not set in local.cfg)"
fi

# That's all folks!!
