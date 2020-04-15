#!/usr/bin/env bash

# Parse options.
BUILD=1
CHECKOUT=1
PARAMS=""
while (( "$#" )); do
    case "$1" in
        --no-build)
            BUILD=0
            shift 1
            ;;
        --no-checkout)
            CHECKOUT=0
            shift 1
            ;;
        --) # end argument parsing
            shift
            break
            ;;
        -*|--*)
            echo "Error: Unsupported argument '$1'" >&2
            exit 1
            ;;
        *) # preserve positional arguments
            PARAMS="$PARAMS $1"
            shift
            ;;
    esac
done
eval set -- "$PARAMS"

# Initialize environment
set -e
THIS_DIR=$(dirname "$(readlink -f "$0")")
if [ "$#" -ne 1 ] || [ ! -f "${THIS_DIR}/sdk/configs/${1}.sh" ]; then
    echo "Fatal error: expects a single argument with existing pulp chip"
    exit
fi
export PULP_RISCV_GCC_TOOLCHAIN=$HERO_INSTALL
cd ${THIS_DIR}/sdk
pulp_chip=${1}
source configs/${1}.sh
source configs/platform-hsa.sh

# checkout packages
for m in \
    json-tools \
    pulp-tools \
    pulp-configs \
    pulp-rules \
    archi \
    hal \
    debug-bridge2 \
    debug-bridge; \
do
    cmd=""
    if [ $CHECKOUT = 1 ]; then
        cmd="$cmd checkout"
    fi
    if [ $BUILD = 1 ]; then
        cmd="$cmd build"
    fi
    plpbuild --m $m $cmd --stdout
done
if [ $CHECKOUT = 1 ]; then
    plpbuild --g runtime checkout --stdout
fi

if [ $BUILD != 1 ]; then
    exit 0
fi

# Building `pulp-rt` will fail, but this is to be expected.
set +e
plpbuild --m pulp-rt build --stdout
echo 'NOTE: The failure of building `pulp-rt` at this point is known and can be tolerated.'
set -e

# Now that the `pulp-rt` headers are installed, we can go ahead and install `archi-host` followed by
# a re-installation of the entire SDK.  At some point, this will fail because two of the runtime
# variants ('tiny' and 'bare') are not aligned with the main runtime, causing the wrong header files
# to be deployed.
plpbuild --m archi-host build --stdout

# We fix this by forcing the `pulp-rt` headers, followed by the final compilation of `libvmm`.
find runtime/pulp-rt/include -type f -exec touch {} +
plpbuild --m pulp-rt build --stdout
plpbuild --m libvmm build --stdout
plpbuild --g runtime build --stdout

# Setup environment
plpbuild --g pkg build
make env

# Install hero config objects files
cd ${THIS_DIR}
source ${THIS_DIR}/sdk/sourceme.sh
mkdir -p ${PULP_SDK_HOME}/install/hero/${pulp_chip}
$HERO_INSTALL/bin/riscv32-unknown-elf-gcc -Wextra -Wall -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function -Wundef -fdata-sections -ffunction-sections -I${PULP_SDK_INSTALL}/include/io -I${PULP_SDK_INSTALL}/include -march=rv32imcxhua20 -D__riscv__ -include refs/${pulp_chip}/cl_config.h -c refs/rt_conf.c -o ${PULP_SDK_HOME}/install/hero/${pulp_chip}/rt_conf.o
cp -r refs/* ${PULP_SDK_HOME}/install/hero/

# Create symlink from current config to hero-sim
# FIXME: remove the special logic for hero-sim after unifying this further
ln -sf ${pulp_chip} ${PULP_SDK_HOME}/install/lib/hero-sim
ln -sf ../${pulp_chip}/rt_conf.o ${PULP_SDK_HOME}/install/hero/hero-sim/

# Build libhero-target
make -C "${THIS_DIR}/../support/libhero-target/pulp" header build install
