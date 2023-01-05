#!/bin/bash -xe

# Copyright 2022 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

THIS_DIR=$(dirname "$(readlink -f "$0")")
SNITCH_SRC=$1

TARGET="riscv32-unknown-elf"
SNITCH_CFLAGS="-target $TARGET --sysroot=${HERO_INSTALL}/$TARGET"

# Add HERO_INTSALL to path for LLVM toolchain
export PATH=${HERO_INSTALL}/bin:${PATH}

# Default environment variables
[[ -z ${CMAKE} ]] && CMAKE=cmake

##############################
# snruntime
##############################
rm -rf build-snruntime && mkdir build-snruntime
cd build-snruntime
${CMAKE} \
  -DCMAKE_C_COMPILER=clang \
  -DCMAKE_CXX_COMPILER=clang++ \
  -DCMAKE_C_FLAGS="$SNITCH_CFLAGS" \
  -DCMAKE_INSTALL_PREFIX=../install \
  -DCMAKE_TOOLCHAIN_FILE=toolchain-llvm \
  -DSNITCH_RUNTIME="snRuntime-hero" \
  -DOMPSTATIC_NUMTHREADS="0" \
  -DMEM_DRAM_ORIGIN="0xc0000000" \
  $SNITCH_SRC/sw/snRuntime
make
make install
cd ..

##############################
# snblas
##############################
rm -rf build-snblas && mkdir build-snblas
cd build-snblas
${CMAKE} \
  -DCMAKE_C_COMPILER=clang \
  -DCMAKE_CXX_COMPILER=clang++ \
  -DCMAKE_C_FLAGS="$SNITCH_CFLAGS" \
  -DCMAKE_INSTALL_PREFIX=../install \
  -DCMAKE_TOOLCHAIN_FILE=toolchain-llvm \
  $SNITCH_SRC/sw/snBLAS
make
