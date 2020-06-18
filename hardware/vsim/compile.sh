#!/usr/bin/env bash

set -e

if [ -z "$VSIM" ]; then
    VSIM="vsim-10.7b"
fi
readonly VSIM

make -C .. vsim/compile.tcl

${VSIM} -c -do 'source compile.tcl; quit'
