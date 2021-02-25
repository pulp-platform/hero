ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

CSRCS := $(filter-out gemm_layers.%,$(wildcard *.c))
EXE = darknet
LDFLAGS = -lm
CFLAGS += -fintegrated-as

-include $(ROOT)/../common/default.mk
