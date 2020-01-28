#!/bin/bash -e

export PULPRT_TARGET=pulp
export PULPRUN_TARGET=pulp

scriptDir="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"

source $scriptDir/common.sh
