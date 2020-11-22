#!/usr/bin/env bash
#
# Copyright (c) 2020 ETH Zurich, University of Bologna
# SPDX-License-Identifier: Apache-2.0
#
# HEROv3 PULP Tests
# akurth@iis.ee.ethz.ch bjoernf@iis.ee.ethz.ch
#
# This script tries to compile the tests in the openmp-examples/tests-pulp
# subdirectory and run them with the simulator. These provide correctness tests
# for the system.
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

# Run in console
unset DISPLAY

# Make and run
for d in pulp api omp_atomic omp_gcc omp_sync omp_worksharing_for omp_worksharing_sections hero_64; do
  make -C openmp-examples/tests-pulp/$d only=pulp clean all
  pushd hardware/vsim
  ../test/gen_slm_files.sh tests-pulp/$d
  ./start_sim.sh
  popd
done

echo "ALL OK!"
