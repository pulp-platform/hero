#!/usr/bin/env bash

# Initialize environment
set -e
if [ -z "$HERO_INSTALL" ]; then
  echo "Fatal error: The 'HERO_INSTALL' environment variable is not defined!"
  exit 1
fi
THIS_DIR=$(dirname "$(readlink -f "$0")")
if [ "$#" -ne 1 ]; then
    echo 'Fatal: expects a single argument'
    exit 1
fi
if [ ! -f "${THIS_DIR}/sdk/configs/${1}.sh" ]; then
    echo "Fatal: Config for PULP chip '$1' does not exist"
    exit 1
fi
export PULP_RISCV_GCC_TOOLCHAIN=$HERO_INSTALL
export CMUX_ROOT=$HERO_INSTALL/../cmux
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
    plpbuild --m $m checkout build --stdout
done
plpbuild --g runtime checkout --stdout

# Building `pulp-rt` will fail, but this is to be expected.
set +e
plpbuild --m pulp-rt build --stdout
echo 'NOTE: The failure of building `pulp-rt` at this point is known and can be tolerated.'

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
$HERO_INSTALL/bin/riscv32-unknown-elf-gcc -Wextra -Wall -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function -Wundef -fdata-sections -ffunction-sections -I${PULP_SDK_INSTALL}/include/io -I${PULP_SDK_INSTALL}/include -march=rv32imcxpulpv2 -D__riscv__ -include refs/${pulp_chip}/cl_config.h -c refs/rt_conf.c -o ${PULP_SDK_HOME}/install/hero/${pulp_chip}/rt_conf.o
cp -r refs/* ${PULP_SDK_HOME}/install/hero/

# Create symlink from current config to hero-sim
# FIXME: remove the special logic for hero-sim after unifying this further
ln -sf ${pulp_chip} ${PULP_SDK_HOME}/install/lib/hero-sim
ln -sf ../${pulp_chip}/rt_conf.o ${PULP_SDK_HOME}/install/hero/hero-sim/

# Build libhero-target
make -C "${THIS_DIR}/../support/libhero-target/pulp" header build install
