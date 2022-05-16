THIS_DIR=$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")

if [[ -z "${HERO_INSTALL}" ]]; then
    echo "Error: HERO_INSTALL variable is not set (set it to toolchain installation path)"
    return
fi
export PATH=${HERO_INSTALL}/bin:$PATH

if [[ -z "${HERO_TARGET_HOST}" ]]; then
  export HERO_TARGET_HOST=root@hero-vcu128-02.ee.ethz.ch
  export HERO_TARGET_PATH="/root"
fi
export HERO_TARGET_PATH_APPS="${HERO_TARGET_PATH}/apps"
export HERO_TARGET_PATH_DRIVER="${HERO_TARGET_PATH}/drivers"
export HERO_TARGET_PATH_LIB="${HERO_TARGET_PATH}/libs"

export PLATFORM=OCCAMY
export BOARD=OCCAMYVCU128

export ARCH="riscv64"
export HERO_TOOLCHAIN_HOST_TARGET="${ARCH}-hero-linux-gnu"
export CROSS_COMPILE="${HERO_TOOLCHAIN_HOST_TARGET}-"

export HERO_TOOLCHAIN_HOST_LINUX_ARCH="${ARCH}"
export KERNEL_ARCH=${ARCH}
export KERNEL_CROSS_COMPILE=${CROSS_COMPILE}
