ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

CSRCS := $(wildcard *.c)
EXE = darknet-layer
LDFLAGS = -lm
CFLAGS += -fintegrated-as

# HERCULES environment variables are ignored when HERCULES_INSTALL is unset.
export HERCULES_DEFAULT_NUM_THREADS=8

-include $(ROOT)/../common/default.mk
