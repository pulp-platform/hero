#!/usr/bin/env bash
set -e

# pulp runtime simulation start script. This should not be used manually

if [ -n "$CI" -o -z "$DISPLAY" ]; then
    # Run in console-only mode.
    vsim-10.7b -c -do 'source run_pulp_runtime.tcl; quit -code $quitCode'
else
    # Run in GUI mode and silence console output.
    vsim-10.7b -do 'source run_pulp_runtime.tcl'
fi
