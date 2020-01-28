#!/bin/bash -e

export PULPRT_TARGET=marsellus
export PULPRUN_TARGET=marsellus

scriptDir="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"

source $scriptDir/common.sh
