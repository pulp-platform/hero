#!/usr/bin/env bash

### SETUP A HERO LLVM RTE ###
THIS_DIR=$(dirname "$(readlink -f "$0")")

NEWLIB_VERS=3.3.0

# LLVM in HERO is built with a different default target triple, thus we must specify 
# the snitch triple specifically
TARGET="riscv32-unknown-elf"
SNITCH_CFLAGS="-target $TARGET -march=rv32imafd -mabi=ilp32d --sysroot=${HERO_INSTALL}/$TARGET"

# stop on all errors
set -ex

# check installation path
if [ -z "$HERO_INSTALL" ]; then
    echo "Fatal error: set HERO_INSTALL to install location of the toolchain"
    exit 1
fi

# prepare
mkdir -p $HERO_INSTALL
chmod -R u+w $HERO_INSTALL

# remove HERO_INSTALL from path to prevent incorrect sysroot to be located
export PATH=${HERO_INSTALL}/bin:${PATH}

echo "Creating symlinks"
old_pwd=$(pwd)
cd ${HERO_INSTALL}/bin;
for TR in $TARGET;
  do for T in clang clang++ cc c++; do
    ln -sv clang $TR-$T ||:;
  done;
done
cd ${old_pwd}

##############################
# newlib
##############################
echo "newlib for Snitch"

old_pwd=$(pwd)
mkdir -p snitch-newlib; cd snitch-newlib

rm -rf newlib
git clone --depth 1 -b newlib-3.3.0 https://sourceware.org/git/newlib-cygwin.git newlib

# Newlib for rv32
rm -rf newlib-build; mkdir -p newlib-build; cd newlib-build
../newlib/configure                                   \
    --target=$TARGET                                  \
    --prefix=${HERO_INSTALL}                          \
    AR_FOR_TARGET=${HERO_INSTALL}/bin/llvm-ar         \
    AS_FOR_TARGET=${HERO_INSTALL}/bin/llvm-as         \
    LD_FOR_TARGET=${HERO_INSTALL}/bin/llvm-ld         \
    RANLIB_FOR_TARGET=${HERO_INSTALL}/bin/llvm-ranlib \
    CC_FOR_TARGET="${HERO_INSTALL}/bin/clang ${SNITCH_CFLAGS}"
make -j
make install

##############################
# Compiler-rt
##############################

echo "Compiler-rt for Snitch"
old_pwd=$(pwd)
mkdir -p snitch-crt; cd snitch-crt
${CMAKE} -G"Unix Makefiles"                                \
  -DCMAKE_SYSTEM_NAME=Linux                                               \
  -DCMAKE_INSTALL_PREFIX=$(${HERO_INSTALL}/bin/clang -print-resource-dir) \
  -DCMAKE_C_COMPILER=${HERO_INSTALL}/bin/clang                            \
  -DCMAKE_CXX_COMPILER=${HERO_INSTALL}/bin/clang                          \
  -DCMAKE_AR=${HERO_INSTALL}/bin/llvm-ar                                  \
  -DCMAKE_NM=${HERO_INSTALL}/bin/llvm-nm                                  \
  -DCMAKE_RANLIB=${HERO_INSTALL}/bin/llvm-ranlib                          \
  -DCMAKE_C_COMPILER_TARGET="$TARGET"                                     \
  -DCMAKE_CXX_COMPILER_TARGET="$TARGET"                                   \
  -DCMAKE_ASM_COMPILER_TARGET="$TARGET"                                   \
  -DCMAKE_C_FLAGS="$SNITCH_CFLAGS"                                        \
  -DCMAKE_CXX_FLAGS="$SNITCH_CFLAGS"                                      \
  -DCMAKE_ASM_FLAGS="$SNITCH_CFLAGS"                                      \
  -DCMAKE_EXE_LINKER_FLAGS="-nostartfiles -nostdlib -fuse-ld=lld"         \
  -DCOMPILER_RT_BAREMETAL_BUILD=ON                                        \
  -DCOMPILER_RT_BUILD_BUILTINS=ON                                         \
  -DCOMPILER_RT_BUILD_MEMPROF=OFF                                         \
  -DCOMPILER_RT_BUILD_LIBFUZZER=OFF                                       \
  -DCOMPILER_RT_BUILD_PROFILE=OFF                                         \
  -DCOMPILER_RT_BUILD_SANITIZERS=OFF                                      \
  -DCOMPILER_RT_BUILD_XRAY=OFF                                            \
  -DCOMPILER_RT_DEFAULT_TARGET_ONLY=ON                                    \
  -DCOMPILER_RT_OS_DIR=""                                                 \
  -DLLVM_CONFIG_PATH=${HERO_INSTALL}/bin/llvm-config                      \
  -S $THIS_DIR/llvm-project/compiler-rt -B .
${CMAKE} --build . --target install -j
cd ${old_pwd}

# finalize install
chmod -R u-w $HERO_INSTALL
