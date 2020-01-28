#!/bin/bash -e

export PULPRT_TARGET=pulpissimo
export PULPRUN_TARGET=pulpissimo

scriptDir="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"

source $scriptDir/common.sh
