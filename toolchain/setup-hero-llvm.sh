### SETUP A HERO LLVM RTE ###
THIS_DIR=$(dirname "$(readlink -f "$0")")

# stop on all errors
set -e

# check installation path
if [ -z "$RISCV" ]; then
    echo "Fatal error: set RISCV to install location of the toolchain"
    exit
fi

BUILD_TYPE="Release"
if [ ! -z "$1" ]; then
    BUILD_TYPE=$1
fi

# prepare
mkdir -p $RISCV
chmod -R u+w $RISCV

# clean environment when running together with an env source script
unset HERO_PULP_INC_DIR
unset HERO_LIBPULP_DIR
# remove RISCV from path to prevent incorrect sysroot to be located
PATH=$(echo "$PATH" | sed -e "s~$RISCV~~")

# setup llvm build
mkdir -p llvm_build
cd llvm_build

# run llvm build and install
echo "Building LLVM project"
# NOTE: use the cmake from the host tools to ensure a recent version
$RISCV/bin/cmake -G Ninja -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
      -DBUILD_SHARED_LIBS=True -DLLVM_USE_SPLIT_DWARF=True \
      -DCMAKE_INSTALL_PREFIX=$RISCV \
      -DCMAKE_FIND_NO_INSTALL_PREFIX=True \
      -DLLVM_OPTIMIZED_TABLEGEN=True -DLLVM_BUILD_TESTS=False \
      -DDEFAULT_SYSROOT=$RISCV/riscv64-hero-linux-gnu \
      -DLLVM_DEFAULT_TARGET_TRIPLE=riscv64-hero-linux-gnu \
      -DLLVM_TARGETS_TO_BUILD="AArch64" -DLLVM_EXPERIMENTAL_TARGETS_TO_BUILD="RISCV" \
      -DLLVM_TEMPORARILY_ALLOW_OLD_TOOLCHAIN=ON \
      -DLLVM_ENABLE_PROJECTS="clang;openmp" \
      $THIS_DIR/llvm-project/llvm
cmake --build . --target install
cd ..

# setup hercules passes build
mkdir -p hc_build
cd hc_build

# run hercules pass build
# FIXME: integrate LLVM passes better in the HERO architecture
echo "Building Hercules LLVM passes"
$RISCV/bin/cmake -DCMAKE_INSTALL_PREFIX=$RISCV -DCMAKE_BUILD_TYPE="$BUILD_TYPE" \
      -DLLVM_DIR:STRING=$RISCV/lib/cmake/llvm \
      $THIS_DIR/hercules/llvm-passes/
$RISCV/bin/cmake --build . --target install
cd ..

# install wrapper script
# FIXME: this wrapper script should be transparantly included in the HC compiler
echo "Installing hc-omp-pass wrapper script"
cp $THIS_DIR/hc-omp-pass $RISCV/bin

# finalize install
chmod -R u-w $RISCV
