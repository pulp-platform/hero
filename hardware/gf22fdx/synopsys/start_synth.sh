#!/usr/bin/env bash

set -e

export SITE=ZH

synopsys-2018.06 dc_shell-xg-t -64 -topo -x "source ./scripts/go_synth.tcl; quit"
