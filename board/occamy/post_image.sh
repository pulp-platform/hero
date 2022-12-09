#!/usr/bin/env bash

set -e

BOARD_DIR="$( dirname "${0}" )"
MKIMAGE="${HOST_DIR}/bin/mkimage"
DTC="${HOST_DIR}/bin/dtc"
IMAGE_ITS="fit_kernel_dtb.its"
OUTPUT_IMAGE="Image.itb"
OUTPUT_DTB="occamy.dtb"

# Fetch infos from config
# TODO (ckoenig) : consider both BR2_TARGET_UBOOT_CUSTOM_REPO_VERSION and BR2_TARGET_UBOOT_CUSTOM_VERSION_VALUE
UBOOT_CUSTOM_VERSION=$(grep BR2_TARGET_UBOOT_CUSTOM_REPO_VERSION ${BR2_CONFIG} | sed 's/.*=//' | tr -d '"')

# Generate uImage with kernel and dtb
cd "${BINARIES_DIR}"
cp -v "${BOARD_DIR}/${IMAGE_ITS}" .
cp -v /scratch/cykoenig/development/iis-ci-3/hw/system/occamy/fpga/bootrom/occamy.dtb ${OUTPUT_DTB}
echo "DTC ${OUTPUT_DTB} from ${BOARD_DIR}/occamy.dts"
${DTC} -I dts -O dtb -o ${OUTPUT_DTB} ${BOARD_DIR}/occamy.dts
echo "ZIP Image"
gzip -c Image > Image.gz
echo "MKIMAGE ${OUTPUT_IMAGE}"
${MKIMAGE} -f ${IMAGE_ITS} ${OUTPUT_IMAGE}
rm ${IMAGE_ITS}