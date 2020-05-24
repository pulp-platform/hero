#!/usr/bin/env bash

mkdir -p ${TARGET_DIR}/lib/firmware
eval BR2_HERO_BITSTREAM=$(grep BR2_HERO_BITSTREAM ${BR2_CONFIG} | sed 's/.*=//' | tr -d '"')
if [ -z "$BR2_HERO_BITSTREAM" ]; then
  exit
fi

# Write optional bitstream in firmware directory
cd ${BINARIES_DIR}
cp $BR2_HERO_BITSTREAM fpga.bit
${HOST_DIR}/bin/mkbootimage --zynqmp ${BR2_EXTERNAL_HERO_PATH}/board/xilzcu102/bitstream.bif ${TARGET_DIR}/lib/firmware/fpga-default.bin

# Install init.d load script
cp ${BR2_EXTERNAL_HERO_PATH}/board/xilzcu102/S95fpga ${TARGET_DIR}/etc/init.d/
