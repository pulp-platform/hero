############################ OpenMP Sources ############################
ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

# Add new library for DMA calls
INCPATHS += -I$(HERO_INSTALL)/../openmp-examples/polybench-acc/common
LIBPATHS += -L$(HERO_INSTALL)/../openmp-examples/polybench-acc/common

# Add new library for libpremnotify
#LIBPATHS += -L$(HERO_INSTALL)/pulp/sdk/pkg/sdk/dev/install/lib/hero-urania
LIBPATHS += -L$(HERO_INSTALL)/../cmux/lib
LIBPATHS += -L$(HERO_INSTALL)/../openmp-examples/polybench-acc/common
INCPATHS += -I$(HERO_INSTALL)/../cmux/inc
INCPATHS += -I$(HERO_INSTALL)/../cmux/src

CSRCS :=  main.c  gemm.c
exeobjs += dmatransfer.o
EXE=baby_gemm
LDFLAGS=-v -lm -lpremnotify --for-linker --trace
CFLAGS+= -fopenmp -fintegrated-as -v

clean::
	-rm -vf darknet __hmpp* $(EXE) *~ *.dis *.ll *.slm
	-rm -rvf $(DEPDIR)

-include $(ROOT)/../common/default.mk

