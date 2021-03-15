# Copyright (c) 2020 ETH Zurich, University of Bologna
# Licensed under the Apache License, Version 2.0.
# SPDX-License-Identifier: Apache-2.0
#
# Authors:
# - Andreas Kurth <akurth@iis.ee.ethz.ch>

source "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")/../common.sh"

cd "$HERO_ROOT/output/$BR_OUTPUT_SUBDIR"

make pulp-driver-dirclean
make pulp-driver-rebuild
make pulp-driver-reinstall

if defined_or_warning_and_exit HERO_BOARD_HOSTNAME "Will not copy driver to board."; then
  if defined_or_warning_and_exit HERO_BOARD_DRIVER_PATH "Will not copy driver to board."; then
    scpv build/pulp-driver-0.1/pulp.ko $HERO_BOARD_HOSTNAME:"$HERO_BOARD_DRIVER_PATH"
  fi
fi
