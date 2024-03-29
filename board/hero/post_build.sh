#!/usr/bin/env bash

# install native GDB from cross-toolchain to target if we have it
TARGET_TUPLE=$(grep BR2_TOOLCHAIN_EXTERNAL_CUSTOM_PREFIX ${BR2_CONFIG} | sed 's/.*=//' | tr -d '"')
DEBUG_ROOT=$HERO_INSTALL/$TARGET_TUPLE/debug-root
if [ -d "$DEBUG_ROOT/usr" ]; then
    echo "Installing native GDB from cross toolchain"
    cp ${STAGING_DIR}/usr/lib/libncurses.so.5* $1/usr/lib/ # we need libncurses.so.5 for gdb
    rsync -a --chmod=u+w $DEBUG_ROOT/usr $1
fi
