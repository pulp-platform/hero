ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

############################ OpenMP Sources ############################
CSRCS = helloworld.c

# Add new library for libpremnotify
LIBPATHS += -L$(HERO_INSTALL)/../cmux/lib
INCPATHS += -I$(HERO_INSTALL)/../cmux/inc
INCPATHS += -I$(HERO_INSTALL)/../cmux/src

LDFLAGS += -lpremnotify

-include $(ROOT)/../common/default.mk
