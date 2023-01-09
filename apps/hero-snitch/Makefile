# Copyright 2020 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Pull common makefile
MKFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
MKFILE_DIR  := $(dir $(MKFILE_PATH))
ROOT        := ${MKFILE_DIR}../..

# Directories
BUILD = ${MKFILE_DIR}/build

# Sources
DTS     = cva6/occamy.dts
SRCS_S  = cva6/bootrom.S
SRCS_C  = cva6/main.c ../fatbin/cva6/uart.c
OBJS_C  = $(SRCS_C:.c=.o)
LDSCRIPT= cva6/link.ld

# Build products
BOOTROM = ${BUILD}/bootrom
DTB     = $(DTS:.dts=.dtb)

# Common Flags
INCLUDES = -I$(ROOT)/support/include -I$(ROOT)/support/libsnitch/include -I$(ROOT)/support/libsnitch/include -I$(ROOT)/support/snitch-driver 

CFLAGS =  -g -Werror -ffreestanding -fno-strict-aliasing $(OPT)
CFLAGS += -fno-omit-frame-pointer -fno-optimize-sibling-calls -fno-stack-protector
CFLAGS += -mno-save-restore -mstrict-align
CFLAGS += -mabi=lp64d -march=rv64imafd
CFLAGS += -mcmodel=medany
CFLAGS += -DDTBLOB=\"$(DTB)\"

LDFLAGS  = -static -nostartfiles -static-libgcc -lgcc
# CROSS_COMPILE = ${RV64_INSTALL}/bin/riscv64-unknown-linux-gnu-
CROSS_COMPILE = ${HERO_INSTALL}/bin/riscv64-hero-linux-gnu-
NPROC   ?= ${shell expr `nproc` / 2 }
DTC_CFLAGS += -I${UBOOT}/include -I${LINUX_SRC}/arch/riscv/include
# to make macros in arch/riscv/include/asm/asm.h happy
DTC_CFLAGS += -D__riscv_xlen=64 -D__SIZEOF_POINTER__=8 -D__SIZEOF_INT__=4 -D__SIZEOF_SHORT__=2

# Bootrom
BOOTROM_PAYLOAD_DST=0x80200000
CFLAGS  += -DBOOTROM_PAYLOAD_DST=$(BOOTROM_PAYLOAD_DST)

# OpenSBI
OPENSBI      = ${ROOT}/opensbi
PLATFORM     = generic
FW_FDT_PATH ?=

# u-boot
# UBOOT           = ${ARIANE_SDK}/u-boot
UBOOT           = ${ROOT}/u-boot
UBOOT_DEFCONFIG = pulp-platform_occamy_defconfig
# UBOOT           = /home/huettern/git/u-boot
# UBOOT_DEFCONFIG = rocket-chip-vcu128-smode_defconfig

# buildroot/linux
BR_SRC            = ${ROOT}/buildroot
BR_OUT            = ${ROOT}/output/br-hrv-vcu128
# BR_OUT            = /home/huettern/git/buildroot/output
BR_DEFCONFIG      = ${ROOT}/configs/occamy_vcu128_defconfig
LINUX_DEFCONFIG   = ${ROOT}/configs/linux_defconfig
BUSYBOX_DEFCONFIG = ${ROOT}/configs/busybox.config
LINUX_SRC         = ${BR_OUT}/build/linux-5.16.9
UBOOT_SPL_BIN     = /scratch/cykoenig/development/master-thesis/output/br-hrv-vcu128/images/u-boot-spl.bin


############################################################
# Phony targets
############################################################
all: ${BOOTROM} ${BOOTROM}.tcl all-sw
.PHONY: all

clean:
	${RM} ${OBJS_C} ${DTB} ${BOOTROM} ${BOOTROM}.* ${DTS}.pre
.PHONY: clean

# Open a GDB session
gdb:
	../fatbin/scripts/ssh_tunnel.sh start
	$(RV64_GDB) -ex "target extended-remote :3334" ; \
		../fatbin/scripts/ssh_tunnel.sh stop
.PHONY: gdb

rtlsim-sources: ${BOOTROM}
.PHONY: rtlsim-sources

############################################################
# Wildcard targets
############################################################
%.dtb: %.dts
	@echo "DTC   <= $<"
	cpp -nostdinc ${DTC_CFLAGS} -undef -x assembler-with-cpp $< $<.pre
	dtc -I dts $<.pre -O dtb -o $@
%.o: %.c
	@echo "CC    <= $<"
	${RV64_CC} ${CFLAGS} $(INCLUDES) -c $< -o $@
%.tcl:  %.bin
	@echo "TCL   <= $<"
	@$(call BINRAY_SIZE_CHECK,$<,1000000)
	@$(BIN2JTAG) -c32 -b 0 -d hw_axi_1 $< > $@


############################################################
# Software
############################################################
snitch-driver:
	@echo "snitch-driver is built as part of br-hrv-vcu128"
libsnitch:
	@echo "libsnitch is built as part of br-hrv-vcu128"
cva6-app:
	$(MAKE) -C cva6-app
snitch-app:
	mkdir -p snitch-app/build
	cd snitch-app/build && $(CMAKE) ..
	$(MAKE) -C snitch-app/build
all-sw: snitch-app snitch-driver libsnitch cva6-app
all-sw-install-rootfs: all-sw
	$(MAKE) -C cva6-app install-rootfs
	mkdir -p ${ROOTFS}/root/snitch
	cp snitch-app/build/*.bin ${ROOTFS}/root/snitch
.PHONY : snitch-app snitch-driver libsnitch cva6-app all-sw all-sw-install-rootfs

############################################################
# FIT image
############################################################
FITIMG = build/linux/Image.itb
MKIMAGE_ITS = image.its
MKIMAGE_FILES = $(LINUX_BIN) $(DTB)
fitimage: $(FITIMG)
.PHONY : fitimage
$(FITIMG):
	mkdir -p $(@D)
	cp $(MKIMAGE_FILES) $(@D)
	cp $(MKIMAGE_ITS) $(@D)
	gzip -c build/linux/Image > build/linux/Image.gz
	$(MKIMAGE) -f $(@D)/$(notdir $(MKIMAGE_ITS)) $(FITIMG)
fitimage-upload:
	scp $(FITIMG) vcu128-01@bordcomputer:/srv/tftp/vcu128-01
.PHONY: fitimage-upload

flash-u-boot:
	vitis-2020.2 vivado -mode batch -source scripts/occamy_vcu128_flash.tcl -tclargs bordcomputer:3232 091847100638A flash.mcs 0x6000000 /scratch/cykoenig/development/master-thesis/output/br-hrv-vcu128/images/u-boot.itb
	rm flash.mcs

############################################################
# Upload payload through rsync/ssh
############################################################
PAYLOAD_FLIST += $(wildcard snitch-app/build/*.bin)
PAYLOAD_FLIST += cva6-app/{bringup,run.sh,run-remote.sh}

upload-payload:
	@echo "Payload: ${PAYLOAD_FLIST}"
	rsync --progress ${PAYLOAD_FLIST} root@hero-vcu128-02.ee.ethz.ch:/root/payload
upload-driver:
	scp ../../output/br-hrv-vcu128/build/snitch-driver-0.1/snitch.ko root@hero-vcu128-02.ee.ethz.ch:/usr/lib
	scp ../../output/br-hrv-vcu128/build/libsnitch-0.1/lib/libsnitch.so root@hero-vcu128-02.ee.ethz.ch:/usr/lib
.PHONY: upload-payload
run-remote:
	ssh root@hero-vcu128-02.ee.ethz.ch sh /root/payload/run-remote.sh hello_world.bin
ssh:
	ssh root@hero-vcu128-02.ee.ethz.ch
.PHONY: run-remote ssh
