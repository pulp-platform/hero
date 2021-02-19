############################ OpenMP Sources ############################
ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

CSRCS :=  main.c gemm.c
EXE=baby_gemm
LDFLAGS= -lm
CFLAGS+= -fintegrated-as

# HERCULES environment variables are ignored when HERCULES_INSTALL is unset.
export HERCULES_DEFAULT_NUM_THREADS=8

clean::
	-rm -vf darknet __hmpp* $(EXE) *~ *.dis *.ll *.slm
	-rm -rvf $(DEPDIR)

-include $(ROOT)/../common/default.mk

