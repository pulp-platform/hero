#!/usr/bin/env bash

set -e

readonly SRC="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"

# Helper function to copy git-indexed files.
copy_git_files() {
  git ls-files -z --recurse-submodules -- $@ | rsync -av --files-from=- -0 . "$TMP_DST/"
}

# Create temporary destination directory.
readonly TMP_DST="$(mktemp -d)"

# Hardware: Copy to destination.
cd "$SRC"
copy_git_files hardware

# Hardware: Prepare simulation script.
cd "$TMP_DST/hardware"
make vsim/compile.tcl

# Hardware: Remove top-level Makefile, Bender binary, and Bender from compile script.
rm Makefile bender
sed -i -e 's|make -C .. vsim/compile.tcl||' vsim/compile.sh

# Add SLM Converter.
mkdir -p "$TMP_DST/install/bin"
cp ~andkurt/bin/slm_conv-0.3 "$TMP_DST/install/bin/slm_conv"

# Toolchain and Makefile: copy to destination.
cd "$SRC"
copy_git_files toolchain Makefile

# Setup script: copy to destination.
rsync -av setup.sh "$TMP_DST/"

# Create archive from temporary destination directory.
tar -C "$TMP_DST" -czf "$SRC/hero_huawei.tar.gz" .

# Remove temporary directories.
rm -rf "$TMP_DST"
