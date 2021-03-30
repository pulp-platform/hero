#!/usr/bin/env bash

curdir=$(dirname "$(readlink -f "$0")")
cd $curdir/../hardware/vsim
../test/gen_slm_files.sh polybench-acc/$1
output=$(mktemp)
DISPLAY= ./start_sim.sh | tee $output

# Performance tracking
NUM_CYCLES=$(cat "$curdir/../hardware/vsim/trace_core_00_0.log" | tr -s ' ' | cut -f3 -s -d' ' | tail -n 1)
echo "$1: $NUM_CYCLES" >> "$curdir/../vsim-polybench-perf-stats.txt"

# Correctness check
simout=$(cat $output | fgrep '# [0,0]' | tail -n +2 | sed -e 's/# \[0,0\] //' \
  | sed -e 's/[[:space:]]*$//')
expout=$(cat "$curdir/../openmp-examples/polybench-acc/$1/$1.exp")
rm $output
if [ "$simout" = "$expout" ]; then
  echo "> OUTPUT: OK";
  exit 0
else
  echo "> OUTPUT: WRONG!"
  echo "--- OUT ---"
  echo $simout
  echo "--- EXP ---"
  echo $expout
  exit 1
fi
