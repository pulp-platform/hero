#!/usr/bin/env bash
#
# Copyright (c) 2020 ETH Zurich, University of Bologna
# SPDX-License-Identifier: Apache-2.0
#
# HEROv3 Compiler Smoke Test
# bjoernf@iis.ee.ethz.ch
#
# This script tries to compile the benchmarks in the openmp-examples
# subdirectory using a lot of different flags, and all of their combinations. It
# is meant to quickly find cases where the compiler crashes, to avoid having to
# wait for the CI tests to complete. These tests are also currently (21 May '20)
# broader in scope than the CI, although they do not test for correctness, only
# that the compiler doesn't crash.
#
# Usage:
#   1. Set HERO_INSTALL environment variable to your HERO install path.
#   2. cd to the root of the repository.
#   3. Source an environment.
#   4. Run script without arguments.
# This script does not build the infrastructure, so that must be done before, in
# accordance with the README.

# Abort on first non-zero exit code.
set -e

# Below are the CFLAGS and MAKE flags that we should try all combinations of.
# ONLY: Selects the benchmarks to be compiled heterogeneously, or only for PULP.
# If only=pulp is given, then also the main function etc. is compiled with the
# HERO RISCV compiler, giving a lot larger code coverage.
only_makeflags=( "only=pulp" "" )
# DEFAS: Compiles the benchmarks with the "default" default address space (host
# for heterogeneous compilation, pulp for pulp-only compilation), or explicitly
# configures it to be host or pulp.
defas_makeflags=( "" "default-as=host" "default-as=pulp" )
# UNROLL: I used these flags when testing the hardware loops merge request, to
# ensure that there were more loops to transform, by avoiding unrolling. I
# therefore included this as well. Don't know if it is relevant outside that
# scope.
unroll_cflags=( "" "-mllvm -unroll-count=1 -mllvm -unroll-full-max-count=1" )
# The PolyBench-ACC benchmarks have a non-DMA and a DMA-based implementation
# within them, which can be selected by defining the DPOLYBENCH_DMA preprocessor
# macro. This vector will compile each benchmark (and combination of other
# vector values) once with DMA, and once without.
polydma_cflags=( "" "-DPOLYBENCH_DMA")
# Compile with and without debug symbols. Issue 25 reports that it is not
# possible to compile programs with debug flags.
debug_cflags=( "-g" "")

# Try the relevant combinations for the tests-pulp
for only in "${only_makeflags[@]}"; do
  makeflags="$only";
  for unroll in "${unroll_cflags[@]}"; do
    for debug in "${debug_cflags[@]}"; do
      cflags="-v $unroll $debug"
      for d in openmp-examples/tests-pulp/*/; do
        if [ $(basename $d) = "include" ]; then
          continue
        fi
        echo -e "\e[96mTEST: $d    $makeflags    $cflags\e[0m"
        make V=1 -C $d clean all $makeflags cflags="$cflags"
      done
    done
  done
done
echo "SUCCESS TESTS-PULP!"

# Try the relevant combinations for the classic openmp-examples.
makeflags=""
cflags=""
## build examples
for defas in "${defas_makeflags[@]}"; do
  makeflags="$defas";
  for unroll in "${unroll_cflags[@]}"; do
    for debug in "${debug_cflags[@]}"; do
      cflags="$unroll $debug"
      for d in helloworld mm-large mm-small sobel-filter darknet-layer; do
        if [ $(basename $d) = "common" ]; then
          continue
        fi
        echo -e "\e[96mTEST: $d    $makeflags    $cflags\e[0m"
        make V=1 -C openmp-examples/$d clean all $makeflags cflags="$cflags"
      done
    done
  done
done
echo "SUCCESS OPENMP-EXAMPLES!"

# Try the relevant combinations for the polybench benchmarks.
for only in "${only_makeflags[@]}"; do
  for defas in "${defas_makeflags[@]}"; do
    makeflags="$only $defas";
    for unroll in "${unroll_cflags[@]}"; do
      for polydma in "${polydma_cflags[@]}"; do
        for debug in "${debug_cflags[@]}"; do
          cflags="-v $unroll $polydma $debug"
          for d in openmp-examples/polybench-acc/*/; do
            if [ $(basename $d) = "common" ]; then
              continue
            fi
            echo -e "\e[96mTEST: $d    $makeflags    $cflags\e[0m"
            make V=1 -C $d clean all $makeflags cflags="$cflags"
          done
        done
      done
    done
  done
done
echo "SUCCESS POLYBENCH!"
echo "SUCCESS ALL!"
