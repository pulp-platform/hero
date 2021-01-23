############################ OpenMP Sources ############################
ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

# Add new library for libpremnotify
#LIBPATHS += -L$(HERO_INSTALL)/pulp/sdk/pkg/sdk/dev/install/lib/hero-urania
LIBPATHS += -L$(HERO_INSTALL)/../cmux/lib
INCPATHS += -I$(HERO_INSTALL)/../cmux/inc
INCPATHS += -I$(HERO_INSTALL)/../cmux/src

CSRCS :=  main.c gemm.c
EXE=baby_gemm
LDFLAGS=-v -lm -lpremnotify --for-linker --trace
CFLAGS+= -fopenmp -fintegrated-as -v

clean::
	-rm -vf darknet __hmpp* $(EXE) *~ *.dis *.ll *.slm
	-rm -rvf $(DEPDIR)

-include $(ROOT)/../common/default.mk

