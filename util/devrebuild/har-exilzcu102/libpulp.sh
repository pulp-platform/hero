# Copyright (c) 2020 ETH Zurich, University of Bologna
# Licensed under the Apache License, Version 2.0.
# SPDX-License-Identifier: Apache-2.0
#
# Authors:
# - Andreas Kurth <akurth@iis.ee.ethz.ch>

source "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")/../common.sh"

cd "$HERO_ROOT/output/$BR_OUTPUT_SUBDIR"

make libpulp-dirclean
make libpulp-rebuild
make libpulp-reinstall

if defined_or_warning_and_exit HERO_BOARD_HOSTNAME "Will not copy shared library to board."; then
  if defined_or_warning_and_exit HERO_BOARD_LIB_PATH "Will not copy shared library to board."; then
    scpv target/usr/lib/libpulp.so $HERO_BOARD_HOSTNAME:"$HERO_BOARD_LIB_PATH"
  fi
fi