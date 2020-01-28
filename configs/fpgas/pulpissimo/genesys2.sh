#!/bin/bash -e

export PULPRT_TARGET=pulpissimo
export PULPRUN_TARGET=pulpissimo

scriptDir="$(dirname "$(dirname "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")")")"

source $scriptDir/common.sh

export PULPRUN_PLATFORM=fpga

export io=uart
