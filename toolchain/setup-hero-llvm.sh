# config (FIXME: make publicly accessible)
GIT_REPO=git@iis-git.ethz.ch:kwolters
GIT_BRANCH=hero-v3

# check installation path
if [ -z "$RISCV" ]; then
    echo "Fatal error: set RISCV to install location of the toolchain"
    exit
fi

# clone required repositories and init submodules
git clone $GIT_REPO/llvm.git -b $GIT_BRANCH
git clone $GIT_REPO/clang.git -b $GIT_BRANCH
git clone $GIT_REPO/openmp.git -b $GIT_BRANCH
pushd openmp
git submodule update --init
popd

# include clang and openmp into llvm build
ln -sf $PWD/clang llvm/tools
ln -sf $PWD/openmp llvm/projects

# setup build
unset HERO_PULP_INC_DIR
unset HERO_LIBPULP_DIR
mkdir -p build
cd build
mkdir -p $RISCV
chmod -R +w $RISCV

# run build and install
cmake -G Ninja -DCMAKE_BUILD_TYPE="Release" \
      -DBUILD_SHARED_LIBS=True -DLLVM_USE_SPLIT_DWARF=True \
      -DCMAKE_INSTALL_PREFIX=$RISCV \
      -DLLVM_OPTIMIZED_TABLEGEN=True -DLLVM_BUILD_TESTS=False \
      -DDEFAULT_SYSROOT=$RISCV/riscv64-hero-linux-gnu \
      -DLLVM_DEFAULT_TARGET_TRIPLE=riscv64-hero-linux-gnu \
      -DLLVM_TARGETS_TO_BUILD="" -DLLVM_EXPERIMENTAL_TARGETS_TO_BUILD="RISCV" \
      -DLLVM_TEMPORARILY_ALLOW_OLD_TOOLCHAIN=ON \
      ../llvm
cmake --build . --target install

# finalize build
chmod -R -w $RISCV
