# Copyright 2020 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Pull common makefile
MKFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
MKFILE_DIR  := $(dir $(MKFILE_PATH))
ROOT        := ${MKFILE_DIR}../../../..
#include $(ROOT)/util/Makefrag.mk

OBJ_C := common.o
APPS  := bringup

# Toolchain
RV64_INSTALL ?= $(HERO_INSTALL)
RV64_CC      ?= $(HERO_INSTALL)/bin/riscv64-buildroot-linux-gnu-gcc
RV64_OBJDUMP ?= $(HERO_INSTALL)/bin/riscv64-buildroot-linux-gnu-objdump
RV64_OBJCOPY ?= $(HERO_INSTALL)/bin/riscv64-buildroot-linux-gnu-objcopy
RV64_AR      ?= $(HERO_INSTALL)/bin/riscv64-buildroot-linux-gnu-ar


# C flags
CFLAGS    += -Wall -O0 -g -rdynamic -fPIC
INC_FLAGS := -I$(ROOT)/support/include -I$(ROOT)/support/libsnitch/include -I$(ROOT)/support/libsnitch/include -I$(ROOT)/support/snitch-driver 

DEPDIR 		:= .deps
DEPFLAGS 	= -MMD -MP
CFLAGS 	  += $(INC_FLAGS) $(DEPFLAGS)
LDFLAGS   += -lsnitch

RFS_TARGET_DIR = $(ROOTFS)/root

all: ${APPS}

# compile
%.o : %.c
	@echo CC $@
	$(RV64_CC) $(CFLAGS) -c $< -o $@

# link
bringup: bringup.o ${OBJ_C} ${LIBSNITCH}
	@echo LD $@
	$(RV64_CC) $(LDFLAGS) -o $@ $< ${OBJ_C}

clean:
	rm *.o *.d ${APPS}

install-rootfs:
	mkdir -p ${RFS_TARGET_DIR}
	cp ${APPS} ${RFS_TARGET_DIR}
	cp run.sh ${RFS_TARGET_DIR}
	#cp ${LIBSNITCH} ${ROOTFS}/usr/lib

# include dependencies
-include $(DEPS)
