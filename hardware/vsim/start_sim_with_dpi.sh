#!/usr/bin/env bash

set -e

if [ -n "$CI" -o -z "$DISPLAY" ]; then
    # Run in console-only mode.
    vsim-10.7b -c -do 'source run_with_dpi.tcl; quit -code $quitCode'
else
    # Run in GUI mode
    # Don't silence stdout because there might be useful stdout from dpi libraries
    vsim-10.7b -do 'source run_with_dpi.tcl'
fi
