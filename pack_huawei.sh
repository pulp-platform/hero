#!/usr/bin/env bash

set -e

readonly SRC="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"

# Create temporary destination directory.
readonly TMP_DST="$(mktemp -d)"

# Hardware: Copy to destination.
cd "$SRC"
git ls-files -z -- hardware | rsync -av --files-from=- -0 . "$TMP_DST/"

# Hardware: Prepare simulation script.
cd "$TMP_DST/hardware"
make vsim/compile.tcl

# Hardware: Remove top-level Makefile, Bender binary, and Bender from compile script.
rm Makefile bender
sed -i -e 's|make -C .. vsim/compile.tcl||' vsim/compile.sh

# Create archive from temporary destination directory.
tar -C "$TMP_DST" -czf "$SRC/hero_huawei.tar.gz" .

# Remove temporary directories.
rm -rf "$TMP_DST"
