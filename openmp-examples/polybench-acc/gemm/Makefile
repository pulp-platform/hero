ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

# Add new library for libpremnotify
LIBPATHS += -L$(HERO_INSTALL)/../cmux/lib
INCPATHS += -I$(HERO_INSTALL)/../cmux/inc
INCPATHS += -I$(HERO_INSTALL)/../cmux/src
LDFLAGS += -lm -lpremnotify

CSRCS = gemm.c

-include $(ROOT)/../common/polybench.mk
-include $(ROOT)/../../common/default.mk


