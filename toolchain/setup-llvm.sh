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

# Apply patch to LLVM
HC_PATCH_LOC="$THIS_DIR/HerculesCompiler-public/setup/llvm-patches/llvm_12.0.1-rc4_clang.patch"
if ! patch -d "$THIS_DIR/llvm-project" -R -p1 -s -f --dry-run < "$HC_PATCH_LOC" >/dev/null; then
  # Patch not already applied.
  patch -d "$THIS_DIR/llvm-project" -p1 < "$HC_PATCH_LOC"
fi

# if CC and CXX are unset, set them to default values.
if [ -z "$CC" ]; then
  export CC=`which gcc`
fi
if [ -z "$CXX" ]; then
  export CXX=`which g++`
fi
echo "Requesting C compiler $CC"
echo "Requesting CXX compiler $CXX"

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
# Notes:
# - Use the cmake from the host tools to ensure a recent version.
# - Do not build PULP libomptarget offloading plugin as part of the LLVM build on the *development*
#   machine.  That plugin will be compiled for each Host architecture through a Buildroot package.
$HERO_INSTALL/bin/cmake -G Ninja -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
      -DBUILD_SHARED_LIBS=True -DLLVM_USE_SPLIT_DWARF=True \
      -DCMAKE_INSTALL_PREFIX=$HERO_INSTALL \
      -DCMAKE_FIND_NO_INSTALL_PREFIX=True \
      -DLLVM_OPTIMIZED_TABLEGEN=True -DLLVM_BUILD_TESTS=False \
      -DDEFAULT_SYSROOT=$HERO_INSTALL/riscv64-hero-linux-gnu \
      -DLLVM_DEFAULT_TARGET_TRIPLE=riscv64-hero-linux-gnu \
      -DLLVM_TARGETS_TO_BUILD="AArch64;RISCV" \
      -DLLVM_TEMPORARILY_ALLOW_OLD_TOOLCHAIN=ON \
      -DLLVM_ENABLE_PROJECTS="clang;openmp;lld" \
      -DLIBOMPTARGET_NVPTX_BUILD=OFF \
      -DLIBOMPTARGET_PULP_BUILD=OFF \
      -DCMAKE_C_COMPILER=$CC \
      -DCMAKE_CXX_COMPILER=$CXX \
      $THIS_DIR/llvm-project/llvm
$HERO_INSTALL/bin/cmake --build . --target install
cd ..

# setup hercules passes build
mkdir -p llvm-support_build
cd llvm-support_build

# run hercules pass build
# FIXME: integrate LLVM passes better in the HERO architecture
echo "Building LLVM support passes"
$HERO_INSTALL/bin/cmake -G Ninja -DCMAKE_INSTALL_PREFIX=$HERO_INSTALL -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
      -DLLVM_DIR:STRING=$HERO_INSTALL/lib/cmake/llvm \
      -DCMAKE_C_COMPILER=$CC \
      -DCMAKE_CXX_COMPILER=$CXX \
      $THIS_DIR/llvm-support/
$HERO_INSTALL/bin/cmake --build . --target install
cd ..

mkdir -p hercules_build
cd hercules_build
# run hercules pass build
echo "Building Hercules LLVM passes"
$HERO_INSTALL/bin/cmake -G Ninja -DCMAKE_INSTALL_PREFIX=$HERO_INSTALL \
      -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
      -DLLVM_DIR:STRING=$HERO_INSTALL/lib/cmake/llvm \
      -DCMAKE_C_COMPILER=$CC \
      -DCMAKE_CXX_COMPILER=$CXX \
      $THIS_DIR/HerculesCompiler-public/llvm-passes/
$HERO_INSTALL/bin/cmake --build . --target install
cd ..

# install HERCULES environment script.
echo "Installing PREM environment script"
cp $THIS_DIR/HerculesCompiler-public/environment.sh $HERO_INSTALL/prem-environment.sh

# install wrapper script
# FIXME: this wrapper script should be transparantly included in the HC compiler
echo "Installing hc-omp-pass wrapper script"
cp $THIS_DIR/hc-omp-pass $HERO_INSTALL/bin

# finalize install
chmod -R u-w $HERO_INSTALL
