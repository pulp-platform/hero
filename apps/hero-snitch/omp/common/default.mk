ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
TARGET_HOST  = riscv64-hero-linux-gnu
TARGET_DEV   = riscv32-snitch-unknown-elf
REPO_ROOT    = ../../../..
SNRT_INSTALL = $(REPO_ROOT)/output/snitch-runtime/install
ifndef HERO_INSTALL
$(error HERO_INSTALL is not set)
endif

# RV64_INSTALL   = /home/huettern/git/ariane-sdk/install
# RV64_INSTALL   = /home/huettern/git/riscv-gnu-toolchain/install
# RV64_INSTALL   = /home/huettern/git/ariane-sdk-gcc11/buildroot/output/host

# RV64_SYSROOT   = $(RV64_INSTALL)/riscv64-hero-linux-gnu/sysroot
# RV64_SYSROOT   = $(HERO_INSTALL)/riscv64-hero-linux-gnu/sysroot
# RV64_SYSROOT   = $(RV64_INSTALL)/sysroot
# RV64_SYSROOT   = /home/huettern/git/ariane-sdk-gcc11/buildroot/output/host
# RV64_SYSROOT   = /home/huettern/git/ariane-sdk-gcc11/buildroot/output/host/riscv64-hero-linux-gnu/sysroot
# RV64_SYSROOT   = /home/huettern/git/ariane-sdk/buildroot/output/host
# RV64_SYSROOT   = /home/huettern/git/ariane-sdk-gcc11/buildroot/output/host/lib/gcc
# RV64_LIBPATH   = -L/home/huettern/git/ariane-sdk-gcc11/buildroot/output/host/riscv64-hero-linux-gnu/sysroot/usr/lib


# Toolchain
LLVM_INSTALL = $(HERO_INSTALL)
CC := $(LLVM_INSTALL)/bin/clang
LINK := $(LLVM_INSTALL)/bin/llvm-link
COB := $(LLVM_INSTALL)/bin/clang-offload-bundler
DIS := $(LLVM_INSTALL)/bin/llvm-dis
HOP := $(HERO_INSTALL)/bin/hc-omp-pass
GCC := $(HERO_INSTALL)/bin/$(TARGET_HOST)-gcc

ARCH_HOST = host-$(TARGET_HOST)
ARCH_DEV = openmp-$(TARGET_DEV)

HOST_OBJDUMP := $(LLVM_INSTALL)/bin/$(TARGET_HOST)-objdump
DEV_OBJDUMP := $(LLVM_INSTALL)/bin/llvm-objdump --mcpu=snitch

opt = 0
# compilation debug
# debug = -v -debug -save-temps=obj

.DEFAULT_GOAL = all

# CFLAGS and LDFLAGS have three components/stages
# 1) without suffix, they apply to heterogeneous compilation;
# 3) with _PULP suffix, they apply only to the PULP part of compilation;
# 4) with _COMMON suffix, they apply to both PULP and host compilation.
CFLAGS_COMMON += $(cflags) -O$(opt) -static
CFLAGS_COMMON += -g
CFLAGS_PULP += $(CFLAGS_COMMON) -target $(TARGET_DEV) -I$(HERO_PULP_INC_DIR)
CFLAGS += -target $(TARGET_HOST) $(CFLAGS_COMMON)
CFLAGS_COMMON += -fopenmp=libomp
CFLAGS += -fopenmp-targets=$(TARGET_DEV)
LDFLAGS_COMMON ?= $(ldflags) -static
LDFLAGS_PULP += $(LDFLAGS_COMMON)
LDFLAGS += $(LDFLAGS_COMMON)

# TODO: Implement libherotarget for snitch
# LDFLAGS += -lhero-target
# ifeq ($(TARGET_HOST),riscv64-hero-linux-gnu)
# 	# FIXME: we explicitly need to embed the correct linker for riscv
# 	LDFLAGS += -Wl,-dynamic-linker,/lib/ld-linux-riscv64-lp64.so.1
# endif

INCPATHS += -I$(REPO_ROOT)/support/libhero-target/inc
INCPATHS += -I$(ROOT) -include hero_64.h
LIBPATHS += $(RV64_LIBPATH)
LIBPATHS ?=

APP = $(shell basename `pwd`)
EXE = $(APP)
SRC = $(CSRCS)

DEPDIR := .deps
DEPFLAGS = -MT $@ -MMD -MP -MF $(DEPDIR)/$*.d

AS_ANNOTATE_ARGS ?=

.PHONY: all exe clean
.PRECIOUS: %.ll

all: $(DEPS) $(EXE) $(EXE).dis $(EXE).snitch.dis

# Compile heterogeneous source and split into host/device .ll
%.ll: %.c $(DEPDIR)/%.d | $(DEPDIR)
	@echo "CC     <= $<"
	SNRT_INSTALL=$(SNRT_INSTALL) $(CC) $(debug) -c -emit-llvm -S $(DEPFLAGS) $(CFLAGS) $(INCPATHS) $<
	@echo "COB    <= $<"
	@$(COB) -inputs=$@ -outputs="$(<:.c=-host.ll),$(<:.c=-dev.ll)" -type=ll -targets="$(ARCH_HOST),$(ARCH_DEV)" -unbundle

.PRECIOUS: %-dev.OMP.ll
%-dev.OMP.ll: %.ll
	@echo "HOP    <= $<"
	@cp $(<:.ll=-dev.ll) $(@:.OMP.ll=.TMP.1.ll)
	@LLVM_INSTALL=$(LLVM_INSTALL)/ $(HOP) $(@:.OMP.ll=.TMP.1.ll) OmpKernelWrapper "HERCULES-omp-kernel-wrapper" $(@:.OMP.ll=.TMP.2.ll)
	@LLVM_INSTALL=$(LLVM_INSTALL)/ $(HOP) $(@:.OMP.ll=.TMP.2.ll) OmpHostPointerLegalizer "HERCULES-omp-host-pointer-legalizer" $(@:.OMP.ll=.TMP.3.ll)
	@cp $(@:.OMP.ll=.TMP.3.ll) $@

.PRECIOUS: %-host.OMP.ll
%-host.OMP.ll: %.ll
	@echo "HOP    <= $<"
	@LLVM_INSTALL=$(LLVM_INSTALL)/ $(HOP) $(<:.ll=-host.ll) OmpKernelWrapper "HERCULES-omp-kernel-wrapper" $(@:.OMP.ll=.TMP.1.ll)
	@cp $(@:.OMP.ll=.TMP.1.ll) $@

%-out.ll: %-host.OMP.ll %-dev.OMP.ll
	@echo "COB    <= $<"
	@$(COB) -inputs="$(@:-out.ll=-host.OMP.ll),$(@:-out.ll=-dev.OMP.ll)" -outputs=$@ -type=ll -targets="$(ARCH_HOST),$(ARCH_DEV)"

exeobjs := $(patsubst %.c, %-out.ll, $(SRC))
$(EXE): $(exeobjs)
	@echo "CCLD   <= $<"
	SNRT_INSTALL=$(SNRT_INSTALL) $(CC) $(debug) $(LIBPATHS) $(CFLAGS) $(exeobjs) $(LDFLAGS) -o $@
	echo "done"

$(EXE).dis: $(EXE)
	@echo "OBJDUMP <= $<"
	@$(HOST_OBJDUMP) -d $^ > $@

# $<.rodata_off in the skip argument to `dd` is the offset of the first section in the ELF file
# determined by readelf -S $(EXE).
$(EXE).snitch.dis: $(EXE)
	@echo "OBJDUMP (device) <= $<"
	@llvm-readelf -S $(EXE) | grep '.rodata' | awk '{print "echo $$[0x"$$4" - 0x"$$5"]"}' | bash > $<.rodata_off
	@llvm-readelf -s $^ | grep '\s\.omp_offloading.device_image\>' \
			| awk '{print "dd if=$^ of=$^_riscv.elf bs=1 count=" $$3 " skip=$$[0x" $$2 " - $$(< $<.rodata_off)]"}' \
			| bash \
			&& $(DEV_OBJDUMP) -S $^_riscv.elf > $@

# Dep
$(DEPDIR):
	@mkdir -p $@

DEPFILES := $(CSRCS:%.c=$(DEPDIR)/%.d)
$(DEPFILES):

include $(wildcard $(DEPFILES))

# Phony
clean::
	-rm -vf __hmpp* $(EXE) *~ *.bc *.dis *.elf *.i *.lh *.lk *.ll *.o *.s *.slm a.out*
	-rm -rvf $(DEPDIR)
	-rm -vf *-host-llvm *-host-gnu

.PHONY: deploy
deploy: $(EXE)
	[ "${DEPLOY_FILES}" ] && scp ${DEPLOY_FILES} root@hero-vcu128-02.ee.ethz.ch:/root || echo "Sending only binary..."
	scp $? root@hero-vcu128-02.ee.ethz.ch:/root

.PHONY: install
install: $(EXE)
	cp $? $(REPO_ROOT)/board/common/overlay/root
