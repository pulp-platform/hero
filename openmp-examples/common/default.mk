############################ OpenMP Sources ############################
CC := clang
LINK := llvm-link
COB := clang-offload-bundler
DIS := llvm-dis

TARGET_HOST = ${HERO_TOOLCHAIN_HOST_TARGET}
TARGET_DEV = riscv32-hero-unknown-elf

ARCH_HOST = host-$(TARGET_HOST)
ARCH_DEV = openmp-$(TARGET_DEV)

ifeq ($(strip $(default-as)),)
ifeq ($(only),pulp)
  default-as=pulp
else
  default-as=host
endif
endif

# CFLAGS and LDFLAGS have three components/stages
# 1) without suffix, they apply to heterogeneous compilation;
# 3) with _PULP suffix, they apply only to the PULP part of compilation;
# 4) with _COMMON suffix, they apply to both PULP and host compilation.
CFLAGS_COMMON += -fopenmp=libomp -O1
ifeq ($(default-as),host)
  CFLAGS_COMMON += -fhero-device-default-as=host
else
  CFLAGS_COMMON += -fhero-device-default-as=device
endif
CFLAGS_PULP += $(CFLAGS_COMMON) -target $(TARGET_DEV) -march=rv32imac
CFLAGS += -target $(TARGET_HOST) $(CFLAGS_COMMON) -fopenmp-targets=$(TARGET_DEV)
# FIXME: we explicitly need to embed the correct linker
LDFLAGS_COMMON += -lhero-target -Wl,-dynamic-linker,/lib/ld-linux-riscv64-lp64.so.1
LDFLAGS_PULP += $(LDFLAGS_COMMON)
LDFLAGS += $(LDFLAGS_COMMON)

INCPATHS += -I../common -include ../common/hero_64.h

BENCHMARK = $(shell basename `pwd`)
EXE = $(BENCHMARK)
SRC = $(CSRCS)

DEPDIR := .deps
DEPFLAGS = -MT $@ -MMD -MP -MF $(DEPDIR)/$*.d

only ?= # can be set to `pulp` to compile a binary only for PULP

.PHONY: all exe clean

ifeq ($(only),pulp)
OBJDUMP := riscv32-hero-unknown-elf-objdump
all : $(EXE) $(EXE).dis slm

.PRECIOUS: %.ll
%.ll: %.c $(DEPDIR)/%.d | $(DEPDIR)
	$(CC) -c -emit-llvm -S $(DEPFLAGS) $(CFLAGS_PULP) $(INCPATHS) $<

%.OMP.ll: %.ll
	hc-omp-pass $< OmpKernelWrapper "HERCULES-omp-kernel-wrapper" $(<:.ll=.TMP.ll)
	hc-omp-pass $(<:.ll=.TMP.ll) OmpHostPointerLegalizer "HERCULES-omp-host-pointer-legalizer" $(<:.ll=.OMP.ll)

$(EXE) : $(SRC:.c=.OMP.ll)
	$(CC) $(CFLAGS_PULP) $(LDFLAGS_PULP) -o $@ $^

slm : $(EXE)_l1.slm $(EXE)_l2.slm

$(EXE)_l2.slm : $(EXE)
	objdump -s --start-address=0x1c000000 --stop-address=0x1cffffff $^ | rg '^ ' | cut -c 2-45 \
      | sort \
      > $@
	../common/one_word_per_line.py $@

$(EXE)_l1.slm : $(EXE)
	objdump -s --start-address=0x10000000 --stop-address=0x1bffffff $^ | rg '^ ' | cut -c 2-45 \
      | perl -p -e 's/^1b/10/' \
      | sort \
      > $@
	../common/one_word_per_line.py $@

else
OBJDUMP := riscv64-unknown-linux-gnu-objdump
all : $(EXE) $(EXE).dis

$(EXE) : $(SRC)
	# generate llvm
	$(CC) -c -emit-llvm -S $(CFLAGS) $(INCPATHS) $^
	# unbundle
	$(COB) -inputs="$(BENCHMARK).ll" -outputs="$(BENCHMARK)-host.ll,$(BENCHMARK)-dev.ll" -type=ll -targets="$(ARCH_HOST),$(ARCH_DEV)" -unbundle
	# apply omp passes
	hc-omp-pass "$(BENCHMARK)-host.ll" OmpKernelWrapper "HERCULES-omp-kernel-wrapper"
	hc-omp-pass "$(BENCHMARK)-dev.ll" OmpKernelWrapper "HERCULES-omp-kernel-wrapper" "$(BENCHMARK)-dev.TMP.ll"
	hc-omp-pass "$(BENCHMARK)-dev.TMP.ll" OmpHostPointerLegalizer "HERCULES-omp-host-pointer-legalizer" "$(BENCHMARK)-dev.OMP.ll"
	# rebundle and compile/link
	$(COB) -inputs="$(BENCHMARK)-host.OMP.ll,$(BENCHMARK)-dev.OMP.ll" -outputs="$(BENCHMARK)-out.ll" -type=ll -targets="$(ARCH_HOST),$(ARCH_DEV)"
	$(CC) $(CFLAGS) $(LDFLAGS) -o $(BENCHMARK) "$(BENCHMARK)-out.ll"
endif

$(EXE).dis : $(EXE)
	$(OBJDUMP) -d $^ > $@

$(DEPDIR):
	@mkdir -p $@

DEPFILES := $(CSRCS:%.c=$(DEPDIR)/%.d)
$(DEPFILES):

include $(wildcard $(DEPFILES))

clean::
	-rm -vf __hmpp* $(EXE) *~ *.dis *.ll *.slm
	-rm -rvf $(DEPDIR)

init-target-host:
ifndef HERO_TARGET_HOST
	$(error HERO_TARGET_HOST is not set)
endif
	ssh -t $(HERO_TARGET_HOST) './sourceme.sh'
	ssh -t $(HERO_TARGET_HOST) 'rmmod -f pulp'
	ssh -t $(HERO_TARGET_HOST) 'insmod $(HERO_TARGET_PATH_DRIVER)/pulp.ko'

prepare:: init-target-host $(EXE)
ifndef HERO_TARGET_HOST
	$(error HERO_TARGET_HOST is not set)
endif
	ssh $(HERO_TARGET_HOST) "mkdir -p $(HERO_TARGET_PATH_APPS)"
	scp $(EXE) $(HERO_TARGET_HOST):$(HERO_TARGET_PATH_APPS)/.

run:: prepare $(EXE)
ifeq ($(call ifndef_any_of,HERO_TARGET_HOST HERO_TARGET_PATH_APPS HERO_TARGET_PATH_LIB),)
	ssh -t $(HERO_TARGET_HOST) 'export LD_LIBRARY_PATH='"'$(HERO_TARGET_PATH_LIB)'"'; cd ${HERO_TARGET_PATH_APPS}; ./$(EXE) $(RUN_ARGS)'
else
	$(error HERO_TARGET_HOST and/or HERO_TARGET_PATH_APPS is not set)
endif
