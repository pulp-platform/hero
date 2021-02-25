ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

CSRCS := $(wildcard *.c)
EXE = darknet
LDFLAGS = -lm
CFLAGS += -fintegrated-as

-include $(ROOT)/../common/default.mk
