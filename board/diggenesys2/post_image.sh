#!/usr/bin/env bash

echo "Creating binary image"
TARGET_TUPLE=$(grep BR2_TOOLCHAIN_EXTERNAL_CUSTOM_PREFIX ${BR2_CONFIG} | sed 's/.*=//' | sed 's/$(ARCH)/riscv64/' | tr -d '"')
$TARGET_TUPLE-objcopy -S -O binary --change-addresses -0x80000000 $1/bbl $1/bbl.bin
