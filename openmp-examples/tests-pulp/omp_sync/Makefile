ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

# Source files to include in test
CSRCS = $(wildcard *.c)

# Include common options and then the common build system
-include $(ROOT)/../include/common.mk
-include $(ROOT)/../../common/default.mk
