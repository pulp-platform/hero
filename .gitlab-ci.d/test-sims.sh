#!/usr/bin/env bash

set -e

def_icache_latches=''
def_icache_ffs='-define RF_1R1W_FF -define RF_2R2W_FF'
def_icache_ffs_l15_data_sram="$def_icache_ffs -define USE_DATA_SRAM"

cd hardware
for defines in "$def_icache_latches" "$def_icache_ffs" "$def_icache_ffs_l15_data_sram"; do
  export DEFINES="$defines"
  for sim in vsim vcs; do
    if [ "$sim" = "vcs" ]; then
      make vcs/compile.sh
    fi
    # Compile testbench
    cd $sim
    ./compile.sh
    for d in "$@"; do
      make -C ../../example-apps/$d clean all
      ../test/gen_slm_files.sh $d
      ./start_sim.sh
    done
    cd -
  done
done
