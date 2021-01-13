ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

############################ OpenMP Sources ############################
CSRCS = seq.c polybench.c
INCPATHS += -I$(HERO_INSTALL)/../openmp-examples/seq
CFLAGS+= -DN=262144 -DTIMEKERN

-include $(ROOT)/../common/default.mk
