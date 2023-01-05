#!/bin/bash -xe

# Copyright 2022 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

THIS_DIR=$(dirname "$(readlink -f "$0")")

# cxx from variable or system
# export CXX=/usr/pack/gcc-9.2.0-af/linux-x64/bin/g++; export CC=/usr/pack/gcc-9.2.0-af/linux-x64/bin/gcc
# if CC and CXX are unset, set them to default values.
if [ -z "$CC" ]; then
  export CC=`which gcc`
fi
if [ -z "$CXX" ]; then
  export CXX=`which g++`
fi
if [ -z "$CMAKE" ]; then
  export CMAKE=`which cmake`
fi
echo "Requesting C compiler $CC"
echo "Requesting CXX compiler $CXX"
echo "Requesting cmake $CMAKE"

##############################
# from here on, use the new built toolchain
##############################

PATH=${HERO_INSTALL}/bin:${PATH}

chmod -R u+w $HERO_INSTALL

##############################
# newlib
##############################
[ ! -d newlib-rv32 ] && git clone --depth 1 -b newlib-3.3.0 https://sourceware.org/git/newlib-cygwin.git newlib-rv32

# Newlib for rv32
cd newlib-rv32

./configure                                           \
    --target=riscv32-unknown-elf                      \
    --prefix=${HERO_INSTALL}                          \
    AR_FOR_TARGET=${HERO_INSTALL}/bin/llvm-ar         \
    AS_FOR_TARGET=${HERO_INSTALL}/bin/llvm-as         \
    LD_FOR_TARGET=${HERO_INSTALL}/bin/llvm-ld         \
    RANLIB_FOR_TARGET=${HERO_INSTALL}/bin/llvm-ranlib \
    CC_FOR_TARGET="${HERO_INSTALL}/bin/clang -march=rv32imafd"

make
make install

cd ..

##############################
# compiler-rt
##############################
mkdir -p compiler-rt32
cd compiler-rt32
# NOTE: CMAKE_SYSTEM_NAME is set to linux to allow the configure step to
#       correctly validate that clang works for cross compiling
${CMAKE} -G"Unix Makefiles"                                                     \
    -DCMAKE_SYSTEM_NAME=Linux                                                \
    -DCMAKE_INSTALL_PREFIX=$(${HERO_INSTALL}/bin/clang -print-resource-dir) \
    -DCMAKE_C_COMPILER=${HERO_INSTALL}/bin/clang                            \
    -DCMAKE_CXX_COMPILER=${HERO_INSTALL}/bin/clang                          \
    -DCMAKE_AR=${HERO_INSTALL}/bin/llvm-ar                                  \
    -DCMAKE_NM=${HERO_INSTALL}/bin/llvm-nm                                  \
    -DCMAKE_RANLIB=${HERO_INSTALL}/bin/llvm-ranlib                          \
    -DCMAKE_C_COMPILER_TARGET="riscv32-unknown-elf"                          \
    -DCMAKE_CXX_COMPILER_TARGET="riscv32-unknown-elf"                        \
    -DCMAKE_ASM_COMPILER_TARGET="riscv32-unknown-elf"                        \
    -DCMAKE_C_FLAGS="-march=rv32imafd -mabi=ilp32d"                          \
    -DCMAKE_CXX_FLAGS="-march=rv32imafd -mabi=ilp32d"                        \
    -DCMAKE_ASM_FLAGS="-march=rv32imafd -mabi=ilp32d"                        \
    -DCMAKE_EXE_LINKER_FLAGS="-nostartfiles -nostdlib -fuse-ld=lld"          \
    -DCMAKE_SYSROOT="${HERO_INSTALL}/riscv32-unknown-elf"                   \
    -DCOMPILER_RT_BAREMETAL_BUILD=ON                                         \
    -DCOMPILER_RT_BUILD_BUILTINS=ON                                          \
    -DCOMPILER_RT_BUILD_MEMPROF=OFF                                          \
    -DCOMPILER_RT_BUILD_LIBFUZZER=OFF                                        \
    -DCOMPILER_RT_BUILD_PROFILE=OFF                                          \
    -DCOMPILER_RT_BUILD_SANITIZERS=OFF                                       \
    -DCOMPILER_RT_BUILD_XRAY=OFF                                             \
    -DCOMPILER_RT_DEFAULT_TARGET_ONLY=ON                                     \
    -DCOMPILER_RT_OS_DIR=""                                                  \
    -DLLVM_CONFIG_PATH=../llvm_build/bin/llvm-config                         \
    ${THIS_DIR}/llvm-project/compiler-rt
${CMAKE} --build . --target install
cd ..

##############################
# setup hercules passes build
##############################

mkdir -p llvm-support_build
cd llvm-support_build

# run hercules pass build
# FIXME: integrate LLVM passes better in the HERO architecture
echo "Building LLVM support passes"
${CMAKE} -G Ninja -DCMAKE_INSTALL_PREFIX=$HERO_INSTALL -DCMAKE_BUILD_TYPE="Release" \
      -DLLVM_DIR:STRING=$HERO_INSTALL/lib/cmake/llvm \
      -DCMAKE_C_COMPILER=$CC -DCMAKE_CXX_COMPILER=$CXX \
      ${THIS_DIR}/llvm-support/
${CMAKE} --build . --target install
cd ..

##############################
# Symlinks
##############################

# Add symlink to sysroot for HERO toolchain
cd ${HERO_INSTALL}
ln -fsv riscv32-unknown-elf riscv32-snitch-unknown-elf

# Add symlinks to LLVM tools
cd ${HERO_INSTALL}/bin
for TRIPLE in riscv32-unknown-elf; do
  for TOOL in clang clang++ cc c++; do
    ln -fsv clang ${TRIPLE}-${TOOL}
  done
done


chmod -R u-w $HERO_INSTALL
