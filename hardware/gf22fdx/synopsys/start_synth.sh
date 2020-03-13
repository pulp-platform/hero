#!/usr/bin/env bash

set -e

# Parse arguments.
SCRIPT='go_synth.tcl'
while (( "$#" )); do
  case "$1" in
    -e|--elab-only)
      SCRIPT='go_elab.tcl'
      shift 1
      ;;
    *)
      echo "Error: Unsupported argument $1" >&2
      exit 1
      ;;
  esac
done

export SITE=ZH

synopsys-2018.06 dc_shell-xg-t -64 -topo -x "source ./scripts/$SCRIPT; quit"
