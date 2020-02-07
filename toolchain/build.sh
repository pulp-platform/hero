#!/usr/bin/env bash
set -e
if [[ -z $HERO_INSTALL ]]; then
   echo "HERO_INSTALL is unset"
   exit 1
fi

PULP_RISCV_GCC=v1.0.16-pulp-riscv-gcc-centos-7.tar.bz2

mkdir -p "$HERO_INSTALL"

if [[ ! -f $PULP_RISCV_GCC ]]; then
    wget https://github.com/pulp-platform/pulp-riscv-gnu-toolchain/releases/download/v1.0.16/v1.0.16-pulp-riscv-gcc-centos-7.tar.bz2
else
    echo "$PULP_RISC_GCC is already downloaded, skipping"
fi

tar -xvf "$PULP_RISCV_GCC" -C "$HERO_INSTALL" --strip 1
