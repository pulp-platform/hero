#!/usr/bin/env bash

set -e

readonly script_path="$( cd "$(dirname "$0")" ; pwd -P )"
readonly slm_path="$script_path/slm_files"
readonly examples_path="$script_path/../../example-apps"

slm_conv='slm_conv-0.3'
if ! which $slm_conv &>/dev/null; then
    slm_conv=~andkurt/bin/slm_conv-0.3
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

# Find binary
if [[ -e "${app_path}/build/test/test" ]]; then
    # Binary in application compiled with the pulp-runtime
    readonly binary="${app_path}/build/test/test"
elif [[ -e "${app_path}/${app_name}" ]]; then
    # Binary in application compiled with the SDK
    readonly binary="${app_path}/${app_name}"
else
    echo "Make sure a binary can be found in the app folder"
fi

# Create L1 SLM
riscv32-unknown-elf-objdump -s --start-address=0x10000000 --stop-address=0x1bffffff "$binary" | rg '^ ' | cut -c 2-45 \
    | perl -p -e 's/^1b/10/' \
    | sort \
    > ${app_name}_l1.slm
    $examples_path/common/one_word_per_line.py ${app_name}_l1.slm

# Create L2 SLM
riscv32-unknown-elf-objdump -s --start-address=0x1c000000 --stop-address=0x1cffffff "$binary" | rg '^ ' | cut -c 2-45 \
    | sort \
    > ${app_name}_l2.slm
    $examples_path/common/one_word_per_line.py ${app_name}_l2.slm

# Split SLM per bank
$slm_conv --swap-endianness -f "${app_name}_l1.slm" \
    -w 32 -P 16 -S 1 -n 2048 -s 0x10000000 -F l1_%01S_%01P.slm
$slm_conv --swap-endianness -f "${app_name}_l2.slm" \
    -w 32 -P  4 -S 4 -n 2048 -s 0x1c000000 -F l2_%01S_%01P.slm
