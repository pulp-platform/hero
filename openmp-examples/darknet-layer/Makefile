ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

CSRCS := main.c gemm.c
EXE = darknet-layer
LDFLAGS = -lm
CFLAGS += -fintegrated-as

-include $(ROOT)/../common/default.mk
