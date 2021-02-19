############################ OpenMP Sources ############################
ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

CSRCS :=  main.c gemm.c
EXE=baby_gemm
LDFLAGS= -lm
CFLAGS+= -fintegrated-as

clean::
	-rm -vf darknet __hmpp* $(EXE) *~ *.dis *.ll *.slm
	-rm -rvf $(DEPDIR)

-include $(ROOT)/../common/default.mk

