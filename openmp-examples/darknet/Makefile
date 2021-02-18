# Copyright (c) 2020 ETH Zurich and University of Bologna
# Licensed under the Apache License, Version 2.0; see LICENSE.Apache-2.0 for details.
# SPDX-License-Identifier: Apache-2.0

ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

CSRCS := $(wildcard *.c)
EXE = darknet
LDFLAGS = -lm
CFLAGS += -fintegrated-as

# HERCULES environment variables are ignored when HERCULES_INSTALL is unset.
export HERCULES_DEFAULT_NUM_THREADS=8

-include $(ROOT)/../common/default.mk
