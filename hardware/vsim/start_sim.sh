#!/usr/bin/env bash

set -e

if [ -n "$CI" -o -z "$DISPLAY" ]; then
    # Run in console-only mode.
    vsim-10.7b -c -do 'source run.tcl; quit -code $quitCode'
else
    # Run in GUI mode and silence console output.
    vsim-10.7b -do 'source run.tcl' &>/dev/null
fi
