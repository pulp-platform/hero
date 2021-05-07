#!/usr/bin/env bash

# Copyright (c) 2020 ETH Zurich, University of Bologna
# SPDX-License-Identifier: Apache-2.0
#
# Test a HERO Release (Candidate)
#
# Author: Andreas Kurth

set -e # abort on first error

usage() {
  echo "$0 <tag/branch/commit to check out> <hostname of board to test on>"
}

if test "$#" -ne "2"; then
  usage
  exit 1
fi
readonly git_obj="$1"
readonly board_hostname="$2"

if git rev-parse --git-dir >/dev/null 2>&1; then
  echo "Error: This script is not intended to be run inside an existing Git repository!"
  exit 1
fi

if ! command -v memora > /dev/null; then
  echo "Error: Memora is not in PATH, but is needed to fetch bitstream."
  exit 1
fi

# Clone repository at the desired git object.
git clone --recursive git@iis-git.ee.ethz.ch:hero/hero.git --branch "$git_obj" hero-"$git_obj"
cd "hero-$git_obj"

# Configure environment.
export HERO_INSTALL="$(pwd)/install"

# Build toolchains and SDKs.
make tc-pulp
make tc-har-olinux
make sdk-pulp
make sdk-har
make tc-llvm
.gitlab-ci.d/memora_retry.sh get bitstream-zcu102 # use bitstream from CI, since it is well isolated
echo "BR2_HERO_BITSTREAM=$(pwd)/hardware/fpga/hero_exilzcu102/hero_exilzcu102.runs/impl_1/hero_exilzcu102_wrapper.bit" > local.cfg
make br-har-exilzcu102

# Deploy build artifacts to board and reboot it.
echo "We will now deploy build artifacts (root FS, kernel, bitstream, etc.) to '$board_hostname'."
read -n 1 -s -r -p "Press any key to continue."
echo ""
mv output/br-har-exilzcu102/images/{boot.bin,BOOT.BIN} # not sure if lower case also works
scp \
  output/br-har-exilzcu102/images/{BOOT.BIN,image.ub} \
  "$board_hostname:/run/media/mmcblk0p1/"
ssh "$board_hostname" '/bin/rm -rf lib/'
scp -r \
  output/br-har-exilzcu102/target/usr/lib/ \
  "$board_hostname:lib/"
scp output/br-har-exilzcu102/target/lib/modules/4.19.0/extra/pulp.ko \
  "$board_hostname:."

echo "Rebooting board and waiting for it to come back up .."
ssh "$board_hostname" '/sbin/reboot'
sleep 10
until ping -c1 "$board_hostname" >/dev/null 2>&1; do :; done
sleep 5

echo "Loading PULP driver .."
ssh "$board_hostname" '/sbin/insmod pulp.ko'

# Build and test applications.
source env/exilzcu102.sh
cd openmp-examples
for d in \
    helloworld \
    mm-large \
    mm-small \
    polybench-acc/{2mm,3mm,atax,bicg,convolution-2d,covariance,gemm} \
    tests-hero/* \
    darknet \
    ; do
  cd $d
  echo "Building '$d' .."
  make clean all >/dev/null 2>&1
  app_name="$(basename $d)"
  echo "Copying '$app_name' to board and executing it .."
  scp "$app_name" "$board_hostname":.
  ssh "$board_hostname" "./run_binary.sh $app_name"
  cd - >/dev/null
done
cd darknet
echo "Building 'darknet' with manual tiling and DMA transfers .."
CFLAGS="$CFLAGS -DGEMM_NN_TILED_OFFLOAD_MANUAL_DMA" make clean all >/dev/null 2>&1
scp darknet "$board_hostname":.
ssh "$board_hostname" "./run_binary.sh darknet"
cd - >/dev/null

cd ..
