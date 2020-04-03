#!/usr/bin/env bash

set -e

readonly SRC="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"

# Helper function to copy git-indexed files.
copy_git_files() {
  git ls-files -z --recurse-submodules -- $@ | rsync -av --files-from=- -0 . "$TMP_DST/"
}

# Create temporary destination directory.
readonly TMP_DST="$(mktemp -d)"

# Env: Copy to destination.
cd "$SRC"
mkdir -p "$TMP_DST/env"
rsync -av env/* "$TMP_DST/env/"

# Hardware: Copy to destination.
copy_git_files hardware

# Hardware: Prepare simulation script.
cd "$TMP_DST/hardware"
make vsim/compile.tcl

# Hardware: Remove top-level Makefile, Bender binary, and Bender from compile script.
rm Makefile bender
sed -i -e 's|make -C .. vsim/compile.tcl||' vsim/compile.sh

# Add SLM Converter and python script.
cd "$SRC"
mkdir -p "$TMP_DST/install/bin"
cp ~andkurt/bin/slm_conv-0.3 "$TMP_DST/install/bin/slm_conv"

# Toolchain and Makefile: copy to destination.
cd "$SRC"
copy_git_files toolchain Makefile

# PULP software: copy to destination.
cd "$SRC"
copy_git_files pulp

# PULP software: Git-init SDK
cd "$TMP_DST/pulp/sdk"
git init
git config --local user.name 'Packager'
git config --local user.email 'packager@localhost'
git add -A
git commit -m 'initial commit'
git submodule update --init --recursive
../setup-sdk.sh --no-build hero-arm64

# Support software: copy to destination.
cd "$SRC"
copy_git_files support

## Setup script: copy to destination.
#cd "$SRC"
#rsync -av setup.sh "$TMP_DST/"

# ReadMe and Prerequisites: copy to destination.
cd "$SRC"
copy_git_files README.md PREREQUISITES.md

# Apps (host, OpenMP examples, pipeline): copy to destination.
cd "$SRC"
copy_git_files apps openmp-examples pipeline interference-experiments

# Buildroot files: copy to destination.
cd "$SRC"
copy_git_files Config.in board buildroot configs external.desc external.mk package petalinux

# Create archive from temporary destination directory.
sleep 1 # give Git time to settle
tar -C "$TMP_DST" -czf "$SRC/hero_siemens.tar.gz" .

# Remove temporary directories.
rm -rf "$TMP_DST"
