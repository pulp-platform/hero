#!/usr/bin/env bash

### SETUP A HERO LLVM RTE ###
THIS_DIR=$(dirname "$(readlink -f "$0")")

# stop on all errors
set -e

# check installation path
if [ -z "$HERO_INSTALL" ]; then
    echo "Fatal error: set HERO_INSTALL to install location of the toolchain"
    exit 1
fi

BUILD_TYPE="Release"
if [ ! -z "$1" ]; then
    BUILD_TYPE=$1
fi

# prepare
mkdir -p $HERO_INSTALL
chmod -R u+w $HERO_INSTALL

# clean environment when running together with an env source script
unset HERO_PULP_INC_DIR
unset HERO_LIBPULP_DIR
# remove HERO_INSTALL from path to prevent incorrect sysroot to be located
PATH=$(echo "$PATH" | sed -e "s~$HERO_INSTALL~~")

# setup llvm build
mkdir -p llvm_build
cd llvm_build

# run llvm build and install
echo "Building LLVM project"
# NOTE: use the cmake from the host tools to ensure a recent version
$HERO_INSTALL/bin/cmake -G Ninja -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
      -DBUILD_SHARED_LIBS=True -DLLVM_USE_SPLIT_DWARF=True \
      -DCMAKE_INSTALL_PREFIX=$HERO_INSTALL \
      -DCMAKE_FIND_NO_INSTALL_PREFIX=True \
      -DLLVM_OPTIMIZED_TABLEGEN=True -DLLVM_BUILD_TESTS=False \
      -DDEFAULT_SYSROOT=$HERO_INSTALL/riscv64-hero-linux-gnu \
      -DLLVM_DEFAULT_TARGET_TRIPLE=riscv64-hero-linux-gnu \
      -DLLVM_TARGETS_TO_BUILD="AArch64;RISCV" \
      -DLLVM_TEMPORARILY_ALLOW_OLD_TOOLCHAIN=ON \
      -DLLVM_ENABLE_PROJECTS="clang;openmp" \
      -DLIBOMPTARGET_NVPTX_BUILD=OFF \
      $THIS_DIR/llvm-project/llvm
cmake --build . --target install
cd ..

# setup hercules passes build
mkdir -p hc_build
cd hc_build

# run hercules pass build
# FIXME: integrate LLVM passes better in the HERO architecture
echo "Building LLVM support passes"
$HERO_INSTALL/bin/cmake -DCMAKE_INSTALL_PREFIX=$HERO_INSTALL -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
      -DLLVM_DIR:STRING=$HERO_INSTALL/lib/cmake/llvm \
      $THIS_DIR/llvm-support/
$HERO_INSTALL/bin/cmake --build . --target install
cd ..

# install wrapper script
# FIXME: this wrapper script should be transparantly included in the HC compiler
echo "Installing hc-omp-pass wrapper script"
cp $THIS_DIR/hc-omp-pass $HERO_INSTALL/bin

# finalize install
chmod -R u-w $HERO_INSTALL
