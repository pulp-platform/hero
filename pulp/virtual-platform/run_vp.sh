#!/usr/bin/env bash
ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

# Argument
if [ "$#" -ne 1 ]; then
    echo "Fatal error: Expects a single argument with application to execute"
    exit
fi

# Find binary
binary="$1"
app_path="${ROOT}/../../example-apps/$1"
if file "$1" | grep -q ELF; then
    # Full path given
    readonly binary="$1"
elif file "${app_path}/build/test/test" | grep -q ELF; then
    # Binary in application compiled with the pulp-runtime
    readonly binary="${app_path}/build/test/test"
elif file "${app_path}/$1" | grep -q ELF; then
    # Binary in application compiled with the SDK
    readonly binary="${app_path}/$1"
else
    echo "Make sure a binary can be found in the app folder or give the full path"
fi

# Print which binary is executed
echo "Run $binary"

# Source the virtual platform's environment
source "$ROOT/setup.sh"

# Custom configurations
out_dir="$ROOT/output"
config_file="$ROOT/plt_config.json"
export PULP_CURRENT_CONFIG_ARGS="gvsoc/trace=.* gvsoc/event=.* gvsoc/vcd/gtkw=true"

pulp-run --platform=gvsoc --config=pulp --binary="$binary" --dir="$out_dir" --trace="/sys/board/chip/cluster/*/insn:$out_dir/log" --trace="/sys/board/chip/soc/fc/insn*:$out_dir/fc" prepare run
# pulp-run --platform=gvsoc --config=pulp --binary="$binary" --dir="$out_dir" --trace="/sys/board/chip/fc/*:$out_dir/fc" prepare run
# pulp-run --platform=gvsoc --config=pulp --binary="$binary" --dir="$out_dir" --config-file="$config_file" prepare run > "$out_dir/log"
