THIS_DIR=$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")

if [[ -z "${RISCV}" ]]; then
    echo "Error: RISCV variable is not set (set it to toolchain installation path)"
    return
fi
export PATH=${RISCV}/bin:$PATH

if [[ -z "${HERO_TARGET_HOST}" ]]; then
  export HERO_TARGET_PATH="/mnt/root/"
fi
export HERO_TARGET_PATH_APPS="${HERO_TARGET_PATH}/apps"
export HERO_TARGET_PATH_DRIVER="${HERO_TARGET_PATH}/drivers"
export HERO_TARGET_PATH_LIB="${HERO_TARGET_PATH}/libs"

export PLATFORM=ARIANE
export BOARD=URANIA

export ARCH="riscv64"
export HERO_TOOLCHAIN_HOST_TARGET="${ARCH}-hero-linux-gnu"
export CROSS_COMPILE="${HERO_HOST_TRIPLE}-"

export HERO_TOOLCHAIN_HOST_LINUX_ARCH="${ARCH}"
export KERNEL_ARCH=${ARCH}
export KERNEL_CROSS_COMPILE=${CROSS_COMPILE}

export HERCULES_ARCH=URANIA

export CFLAGS=""
# FIXME: we need this LDFLAGS to ensure clang embeds the correct linker
export LDFLAGS="-Wl,-dynamic-linker,/lib/ld-linux-riscv64-lp64.so.1"

export PULP_RISCV_GCC_TOOLCHAIN=${RISCV}

if [[ -z "${HERO_PULP_SDK_DIR}" ]]; then
    export HERO_PULP_SDK_DIR=$(readlink -f "$THIS_DIR/../support/pulp-sdk")
fi

if [ -f ${HERO_PULP_SDK_DIR}/sourceme.sh ]; then
    export HERO_PULP_INC_DIR=${HERO_PULP_SDK_DIR}/pkg/sdk/dev/install/include
    source ${HERO_PULP_SDK_DIR}/sourceme.sh
fi
