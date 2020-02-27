THIS_DIR=$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")

if [[ -z "${HERO_INSTALL}" ]]; then
    echo "Error: HERO_INSTALL variable is not set (set it to toolchain installation path)"
    return
fi

if [[ ":$PATH:" != *":${HERO_INSTALL}/bin:"* ]]; then
    export PATH=${HERO_INSTALL}/bin:$PATH
fi

export PLATFORM=ARM
export BOARD=HUAWEI

export ARCH="arm"

export PULP_RISCV_GCC_TOOLCHAIN=${HERO_INSTALL}

export HERO_PULP_SDK_DIR=$(readlink -f "$THIS_DIR/../pulp/sdk")

source ${HERO_PULP_SDK_DIR}/init.sh > /dev/null
if [ -f ${HERO_PULP_SDK_DIR}/sourceme.sh ]; then
    export HERO_PULP_INC_DIR=${HERO_PULP_SDK_DIR}/pkg/sdk/dev/install/include
    source ${HERO_PULP_SDK_DIR}/sourceme.sh
fi


unset CFLAGS
unset LDFLAGS
