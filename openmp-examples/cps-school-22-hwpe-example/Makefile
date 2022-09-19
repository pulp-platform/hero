ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

############################ OpenMP Sources ############################
CSRCS = main.c traffic_gen_api.c
CFLAGS +=  -I$(PULP_SDK_HOME)/install/include

# Link PULP libraries
CFLAGS_PULP += -g -include $(PULP_SDK_HOME)/install/hero/hero-sim/cl_config.h
LDFLAGS_PULP += -lomptarget-pulp -lrt

# Link AROV library
LDFLAGS_PULP += -larov-target
LDFLAGS += -larov-target

LDFLAGS_PULP += -lhwpe_cl0_lic0 \
				-lhwpe_cl0_lic1 \
				-lhwpe_cl0_lic2 \
				-lhwpe_cl0_lic3

LDFLAGS += 	-lhwpe_cl0_lic0 \
			-lhwpe_cl0_lic1 \
			-lhwpe_cl0_lic2 \
			-lhwpe_cl0_lic3 

-include $(ROOT)/../common/default.mk
