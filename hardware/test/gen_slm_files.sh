#!/usr/bin/env bash

set -e

readonly script_path="$( cd "$(dirname "$0")" ; pwd -P )"
readonly slm_path="$script_path/slm_files"
readonly examples_path="$script_path/../../openmp-examples"

slm_conv='slm_conv-0.3'
if ! which $slm_conv &>/dev/null; then
    # Try unversioned variant of 'slm_conv' executable.
    slm_conv='slm_conv'
    if ! which $slm_conv &>/dev/null; then
        # Neither versioned nor unversioned variant found.
        echo "Error: 'slm_conv' not found in PATH.  Please install it (e.g. with 'cargo install --git https://github.com/andreaskurth/slm_conv')." >&2
        exit 1
    fi
    # Fall back to unversioned variant.
    echo "Warning: 'slm_conv-0.3' not found; falling back to generic 'slm_conv'." >&2
fi
declare -r slm_conv

if [ $# -ne 1 ]; then
    echo "Usage: $0 <app_name>"
    exit 1
else
    readonly app_dir="$1"
fi
readonly app_path="$examples_path/$app_dir"
readonly app_name=$(basename $app_dir)

mkdir -p "$slm_path"
cd "$slm_path"

$slm_conv --swap-endianness -f "$app_path/${app_name}_l1.slm" \
    -w 32 -P 16 -S 1 -n 2048 -s 0x10000000 -F l1_%01S_%01P.slm
$slm_conv --swap-endianness -f "$app_path/${app_name}_l2.slm" \
    -w 32 -P  4 -S 8 -n 1024 -s 0x1c000000 -F l2_%01S_%01P.slm
