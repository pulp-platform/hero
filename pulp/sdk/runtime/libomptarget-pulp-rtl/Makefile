PULP_PROPERTIES += pulp_chip
include $(PULP_SDK_HOME)/install/rules/pulp_properties.mk

OMP_CONFIG           = -DOMP_NOWAIT_SUPPORT
PULP_LIBS            = omptarget-pulp
PULP_LIB_CL_SRCS_omptarget-pulp   += root.c
PULP_CL_CFLAGS_omptarget-pulp = -Wall -O2 -g ${OMP_CONFIG} -I$(CURDIR)/config/pulp


-include $(PULP_SDK_HOME)/install/rules/pulp.mk

header::
	mkdir -p $(PULP_SDK_HOME)/install/include/libomptarget-pulp
	cp *.h $(PULP_SDK_HOME)/install/include/libomptarget-pulp
