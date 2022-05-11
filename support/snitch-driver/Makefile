# Copyright 2020 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Buildroot-compatible kernel module makefile

obj-m := snitch.o

ARCH          := ${KERNEL_ARCH}
CROSS_COMPILE := ${KERNEL_CROSS_COMPILE}

# -I${HERO_LIBPULP_DIR}/inc -I${HERO_PULP_INC_DIR}
ccflags-y += -DPLATFORM=${PLATFORM} ${CFLAGS} -O2
snitch-objs := snitch_module.o

.PHONY: all deploy dis clean build

all: modules
build: modules

modules: $(patsubst %.o,%.c,$(snitch-objs)) $(patsubst %.o,%.h,$(snitch-objs))
	$(MAKE) -S ARCH=$(ARCH) CROSS_COMPILE=$(CROSS_COMPILE) -C $(KERNEL_DIR) M=$(shell pwd) modules

dis: modules
	$(CROSS_COMPILE)objdump -DS snitch.ko > snitch.disasm

clean:
	rm -f modules.order
	rm -f snitch.mod.*
	rm -f *.o
	rm -f snitch.ko
	rm -f Module.symvers
	rm -f .*.o.cmd
	rm -f .*.ko.cmd
	rm -f *.disasm
	rm -f *.o_shipped
