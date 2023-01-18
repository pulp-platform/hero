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

# check installation path
if [ -z "${HERO_DEVICE_DTS}" ]; then
    echo "Fatal error: set HERO_DEVICE_DTS to the location of the occamy.dts"
    exit 1
fi

# Generate uImage with kernel and dtb
cd "${BINARIES_DIR}"
cp -v "${BOARD_DIR}/${IMAGE_ITS}" .
echo "DTC ${OUTPUT_DTB} from ${HERO_DEVICE_DTS}"
${DTC} -I dts -O dtb -o ${OUTPUT_DTB} ${HERO_DEVICE_DTS}
echo "ZIP Image"
gzip -c Image > Image.gz
echo "MKIMAGE ${OUTPUT_IMAGE}"
${MKIMAGE} -f ${IMAGE_ITS} ${OUTPUT_IMAGE}
rm ${IMAGE_ITS}