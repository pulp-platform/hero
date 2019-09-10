obj-m := pulp.o

PLATFORM      := ${PLATFORM}

ARCH          := ${KERNEL_ARCH}
CROSS_COMPILE := ${KERNEL_CROSS_COMPILE}

KERNEL_DIR    := ${KERNEL_DIR}

ccflags-y += -DPLATFORM=${PLATFORM} ${CFLAGS} -O2 -I${HERO_LIBPULP_DIR}/inc -I${HERO_PULP_INC_DIR}
pulp-objs := pulp_module.o pulp_ctrl.o pulp_mem.o pulp_rab.o pulp_dma.o pulp_mbox.o pulp_profile.o

ifeq ($(KERNEL_ARCH),arm64)
	# JUNO and ZynqMP require the stripped down pulp_cache.S
	pulp-objs += pulp_cache.o
endif

ifeq ($(PLATFORM),5)
	# ZynqMP requires pulp_smmu.*
	pulp-objs += pulp_smmu.o
endif

.PHONY: all build deploy dis

all: deploy

build: modules

modules: $(patsubst %.o,%.c,$(pulp-objs)) $(patsubst %.o,%.h,$(pulp-objs))
	$(MAKE) -S ARCH=$(ARCH) CROSS_COMPILE=$(CROSS_COMPILE) -C $(KERNEL_DIR) M=$(shell pwd) modules

deploy: build
	scp pulp.ko ${HERO_TARGET_HOST}:${HERO_TARGET_PATH_DRIVERS}/

dis: build
	$(CROSS_COMPILE)objdump -DS pulp.ko > pulp.disasm

clean:
	rm -f modules.order
	rm -f pulp.mod.*
	rm -f *.o
	rm -f pulp.ko
	rm -f Module.symvers
	rm -f .*.o.cmd
	rm -f .*.ko.cmd
	rm -f *.disasm
	rm -f *.o_shipped
