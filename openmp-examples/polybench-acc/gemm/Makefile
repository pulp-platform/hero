ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

CSRCS = gemm.c

-include $(ROOT)/../common/polybench.mk
-include $(ROOT)/../../common/default.mk
