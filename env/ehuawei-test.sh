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

source ${THIS_DIR}/../pulp/pulp-runtime/configs/hero.sh
export VSIM_PATH=${THIS_DIR}/../hardware/vsim

unset CFLAGS
unset LDFLAGS
