############################ OpenMP Sources ############################
CC := clang
LINK := llvm-link
COB := clang-offload-bundler
DIS := llvm-dis

TARGET_HOST = ${HERO_TOOLCHAIN_HOST_TARGET}
TARGET_DEV = riscv32-hero-unknown-elf

ARCH_HOST = host-$(TARGET_HOST)
ARCH_DEV = openmp-$(TARGET_DEV)

# CFLAGS and LDFLAGS have three components/stages
# 1) without suffix, they apply to heterogeneous compilation;
# 3) with _PULP suffix, they apply only to the PULP part of compilation;
# 4) with _COMMON suffix, they apply to both PULP and host compilation.
CFLAGS_COMMON += -fopenmp=libomp -O0 -g
CFLAGS_PULP += $(CFLAGS_COMMON) -target riscv32-hero-unknown-elf
CFLAGS += -target $(TARGET_HOST) $(CFLAGS_COMMON) -fopenmp-targets=$(TARGET_DEV)
LDFLAGS_COMMON += -lhero-target
LDFLAGS_PULP += $(LDFLAGS_COMMON)
LDFLAGS += $(LDFLAGS_COMMON)

INCPATHS += -I../common

BENCHMARK = $(shell basename `pwd`)
EXE = $(BENCHMARK)
SRC = $(CSRCS)

DEP_FLAG    := -MM

only ?= # can be set to `pulp` to compile a binary only for PULP

.PHONY: all exe clean veryclean

ifeq ($(only),pulp)
all : $(EXE) slm

$(EXE) : $(SRC)
	$(CC) -c -emit-llvm -S $(CFLAGS_PULP) -I../common $(SRC)
	$(CC) $(CFLAGS_PULP) $(LDFLAGS_PULP) -o $@ $@.ll

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
all : $(EXE)

$(EXE) : $(SRC)
	# generate llvm
	$(CC) -c -emit-llvm -S $(CFLAGS) $(INCPATHS) $^
	# unbundle
	$(COB) -inputs="$(BENCHMARK).ll" -outputs="$(BENCHMARK)-host.ll,$(BENCHMARK)-dev.ll" -type=ll -targets="$(ARCH_HOST),$(ARCH_DEV)" -unbundle
	# apply omp passes
	hc-omp-pass "$(BENCHMARK)-host.ll" OmpKernelWrapper "HERCULES-omp-kernel-wrapper"
	hc-omp-pass "$(BENCHMARK)-dev.ll" OmpKernelWrapper "HERCULES-omp-kernel-wrapper"
	# rebundle and compile/link
	$(COB) -inputs="$(BENCHMARK)-host.OMP.ll,$(BENCHMARK)-dev.OMP.ll" -outputs="$(BENCHMARK)-out.ll" -type=ll -targets="$(ARCH_HOST),$(ARCH_DEV)"
	$(CC) $(CFLAGS) $(LDFLAGS) -o $(BENCHMARK) "$(BENCHMARK)-out.ll"
endif

clean::
	-rm -vf __hmpp* -vf $(EXE) *~ *.ll *.slm

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

