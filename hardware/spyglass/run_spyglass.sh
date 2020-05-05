#!/usr/bin/env bash

set -e

spyglass-2019.06 sg_shell -tcl spyglass.tcl
! grep -q FATAL "spyglass-1/pulp/Design_Read/spyglass.log"
