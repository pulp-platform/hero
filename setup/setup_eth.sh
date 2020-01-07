#!/bin/bash
export PULP_RISCV_GCC_TOOLCHAIN=/usr/pack/pulpsdk-1.0-kgf/artifactory/pulp-sdk-release/pkg/pulp_riscv_gcc/1.0.13
export VSIM_PATH=$(pwd)/sim
source ./sdk/pulp-sdk/pkg/sdk/dev/configs/pulp.sh
source ./sdk/pulp-sdk/pkg/sdk/dev/configs/platform-rtl.sh
source ./sdk/pulp-sdk/pkg/sdk/dev/sourceme.sh
