#!/bin/bash -e

scriptDir="$(dirname "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")")"

export PULPRT_HOME=$scriptDir
export PULP_SDK_HOME=$PULPRT_HOME