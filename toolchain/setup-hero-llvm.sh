### SETUP A HERO LLVM RTE ###
THIS_DIR=$(dirname "$(readlink -f "$0")")

# config (FIXME: make publicly accessible)
GIT_REPO=git@iis-git.ethz.ch:kwolters
GIT_BRANCH=hero-v3

# check installation path
if [ -z "$RISCV" ]; then
    echo "Fatal error: set RISCV to install location of the toolchain"
    exit
fi

# clone required repositories and init submodules
git clone $GIT_REPO/HerculesCompiler-public.git -b $GIT_BRANCH

# stop on all errors
set -e

# prepare
mkdir -p $RISCV
chmod -R u+w $RISCV

# setup llvm build
unset HERO_PULP_INC_DIR
unset HERO_LIBPULP_DIR
mkdir -p llvm_build
cd llvm_build

# run llvm build and install
echo "Building LLVM project"
# NOTE: use the cmake from the host tools to ensure a recent version
$RISCV/bin/cmake -G Ninja -DCMAKE_BUILD_TYPE="Release" \
      -DBUILD_SHARED_LIBS=True -DLLVM_USE_SPLIT_DWARF=True \
      -DCMAKE_INSTALL_PREFIX=$RISCV \
      -DCMAKE_FIND_NO_INSTALL_PREFIX=True \
      -DLLVM_OPTIMIZED_TABLEGEN=True -DLLVM_BUILD_TESTS=False \
      -DDEFAULT_SYSROOT=$RISCV/riscv64-hero-linux-gnu \
      -DLLVM_DEFAULT_TARGET_TRIPLE=riscv64-hero-linux-gnu \
      -DLLVM_TARGETS_TO_BUILD="" -DLLVM_EXPERIMENTAL_TARGETS_TO_BUILD="RISCV" \
      -DLLVM_TEMPORARILY_ALLOW_OLD_TOOLCHAIN=ON \
      -DLLVM_ENABLE_PROJECTS="clang;openmp" \
      $THIS_DIR/llvm
cmake --build . --target install
cd ..

# setup hercules passes build
mkdir -p hc_build
cd hc_build

# run hercules pass build
echo "Building Hercules LLVM passes"
cmake -DCMAKE_INSTALL_PREFIX=$RISCV -DLLVM_DIR:STRING=$RISCV/lib/cmake/llvm ../HerculesCompiler-public/llvm-passes/
cmake --build . --target install
cd ..

# install wrapper script
# FIXME: this wrapper script should be transparantly included in the HC compiler
echo "Installing hc-omp-pass wrapper script"
cp $THIS_DIR/hc-omp-pass $RISCV/bin

# finalize install
chmod -R u-w $RISCV
