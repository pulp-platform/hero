#!/bin/bash -e

export PULPRT_TARGET=hero
export PULPRUN_TARGET=hero

scriptDir="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"

source $scriptDir/common.sh
