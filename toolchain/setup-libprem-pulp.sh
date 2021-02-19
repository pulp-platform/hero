#!/bin/sh
START_WD=$(pwd)
source "$1/env/exilzcu102.sh"
export CMUX_HOME="$1/toolchain/HerculesCompiler-public/runtime/cmux"
cd "$CMUX_HOME/src/pulp"
rm -rf build && make && make install
cd "$START_WD"
