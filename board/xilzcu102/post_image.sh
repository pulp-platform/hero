#!/bin/sh
ln -sf hero.dtb ${BINARIES_DIR}/system.dtb

support/scripts/genimage.sh -c board/zynqmp/genimage.cfg
