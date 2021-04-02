# Copyright (c) 2020 ETH Zurich, University of Bologna
# Licensed under the Apache License, Version 2.0.
# SPDX-License-Identifier: Apache-2.0
#
# Authors:
# - Andreas Kurth <akurth@iis.ee.ethz.ch>

source "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")/../common.sh"

if test "$($HERO_ROOT/util/configfile/get_value -s $HERO_ROOT/local.cfg BR2_PACKAGE_PREM_CMUX)" != "y";
    then
  say "Warning: 'prem-cmux' package is not enabled, skipping its build and installation."
else
  cd "$HERO_ROOT/output/$BR_OUTPUT_SUBDIR"
  make prem-cmux-dirclean
  make prem-cmux-rebuild
  make prem-cmux-reinstall

  if defined_or_warning_and_exit \
      HERO_INSTALL "Will not install headers, libs and cmux binary on development machine."; then
    chmod -R u+w "$HERO_INSTALL"
    SRC_USR="host/aarch64-buildroot-linux-gnu/sysroot/usr"
    DST_USR="$HERO_INSTALL/aarch64-buildroot-linux-gnu/sysroot/usr"
    mkdir -p "$DST_USR/include/prem"
    cp -v "$SRC_USR/include/prem"/* "$DST_USR/include/prem/"
    cp -v "$SRC_USR/lib"/{libcmux-vote.a,{libomptarget*,libpremnotify}.so} "$DST_USR/lib/"
    cp -v "$SRC_USR/bin/cmux" "$DST_USR/bin/"
    chmod -R u-w "$HERO_INSTALL"
  fi

  WARN_NO_SCP="Will not copy shared libraries and cmux binary to board."
  if defined_or_warning_and_exit HERO_BOARD_HOSTNAME "$WARN_NO_SCP"; then
    if defined_or_warning_and_exit HERO_BOARD_LIB_PATH "$WARN_NO_SCP"; then
      scpv target/usr/bin/cmux $HERO_BOARD_HOSTNAME:.
      scpv target/usr/lib/{libomptarget*,libpremnotify}.so \
          $HERO_BOARD_HOSTNAME:"$HERO_BOARD_LIB_PATH"
    fi
  fi
fi
