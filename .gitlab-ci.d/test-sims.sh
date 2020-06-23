#!/usr/bin/env bash

set -e

cd hardware
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
