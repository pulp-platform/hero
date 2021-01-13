DT_ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

PULP_PROPERTIES += pulp_chip
include $(PULP_SDK_HOME)/install/rules/pulp_properties.mk

PULP_LIBS = dmatransfer
PULP_LIB_CL_SRCS_dmatransfer += $(DT_ROOT)/dma-lib/dmatransfer-device.c
PULP_CL_CFLAGS_dmatransfer = -Wall -O3 -I$(DT_ROOT)

-include $(PULP_SDK_HOME)/install/rules/pulp.mk

