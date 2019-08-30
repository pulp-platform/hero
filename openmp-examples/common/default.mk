############################ OpenMP Sources ############################
CC := clang
LINK := llvm-link
COB := clang-offload-bundler
DIS := llvm-dis

TARGET_HOST = ${HERO_TOOLCHAIN_HOST_TARGET}
TARGET_DEV = riscv32-hero-unknown-elf

ARCH_HOST = host-$(TARGET_HOST)
ARCH_DEV = openmp-$(TARGET_DEV)

CFLAGS += -target $(TARGET_HOST) -fopenmp=libomp -fopenmp-targets=$(TARGET_DEV) -O0 -g
LDFLAGS += -lhero-target

INCPATHS += -I../common

BENCHMARK = $(shell basename `pwd`)
EXE = $(BENCHMARK)
SRC = $(CSRCS)

DEP_FLAG    := -MM

.PHONY: all exe clean veryclean

all : exe

exe : $(EXE)

$(EXE) : $(SRC)
ifndef HERO_TOOLCHAIN_HOST_TARGET
	$(error HERO_TOOLCHAIN_HOST_TARGET is not set)
endif
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

clean::
	-rm -vf __hmpp* -vf $(EXE) *~ *.ll

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

