#!/usr/bin/env bash

set -e

if [ -z "$DISPLAY" ]; then
    readonly exec_flag="-c"
else
    readonly exec_flag=""
fi

vsim-10.7b "$exec_flag" -do 'source run.tcl' &>/dev/null
