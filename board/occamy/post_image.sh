#!/usr/bin/env bash

set -e

BOARD_DIR="$( dirname "${0}" )"
MKIMAGE="${HOST_DIR}/bin/mkimage"
DTC="${HOST_DIR}/bin/dtc"
IMAGE_ITS="fit_kernel_dtb.its"
OUTPUT_IMAGE="Image.itb"
OUTPUT_DTB="occamy_hero.dtb"

# Fetch infos from config
UBOOT_CUSTOM_VERSION=$(grep BR2_TARGET_UBOOT_CUSTOM_VERSION_VALUE ${BR2_CONFIG} | sed 's/.*=//' | tr -d '"')

# DTC
echo " DTC     ${OUTPUT_DTB}"
cd "${BINARIES_DIR}"
DTSI=${BUILD_DIR}/uboot-${UBOOT_CUSTOM_VERSION}/arch/riscv/dts
${DTC} -I dts -O dtb -o ${OUTPUT_DTB} --include ${DTSI} ${BOARD_DIR}/occamy_hero.dts

# Generate uImage with kernel and dtb
echo " MKIMAGE ${OUTPUT_IMAGE}"
cp -v "${BOARD_DIR}/${IMAGE_ITS}" "${BINARIES_DIR}"
cd "${BINARIES_DIR}"
gzip -c Image > Image.gz
${MKIMAGE} -f ${IMAGE_ITS} ${OUTPUT_IMAGE}
rm ${IMAGE_ITS}
