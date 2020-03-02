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

# Temporarily remove variables from different environments
unset PULP_SDK_HOME
unset INSTALL_DIR
unset PULP_SDK_INSTALL

# Source the virtual platform's environment
source "$ROOT/configs/pulp.sh"
source "$ROOT/setup.sh"

# Custom configurations
out_dir="$ROOT/output"
trace="/sys/board/chip/cluster/pe.*/insn:$out_dir/cluster"

# Print configuration
echo "Write the following traces: $trace to $out_dir"

pulp-run --platform=gvsoc --config=pulp --binary="$binary" --dir="$out_dir" --trace="$trace" prepare run
# pulp-run --platform=gvsoc --config=pulp --binary="$binary" --dir="$out_dir" --trace="/sys/board/chip/cluster/pe.*/insn:$out_dir/cluster" --trace="/sys/board/chip/soc/fc/insn*:$out_dir/fc" prepare run
