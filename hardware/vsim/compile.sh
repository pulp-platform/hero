#!/usr/bin/env bash

set -e

make -C .. vsim/compile.tcl

vsim-10.7b -c -do 'source compile.tcl; quit'
