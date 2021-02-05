PULP_PROPERTIES += pulp_chip
include $(PULP_SDK_HOME)/install/rules/pulp_properties.mk

OMP_CONFIG           = -DOMP_NOWAIT_SUPPORT
PULP_LIBS            = gomp
PULP_LIB_CL_SRCS_gomp   += root.c
PULP_CL_CFLAGS_gomp = -Wall -O2 -g ${OMP_CONFIG} -I$(CURDIR)/config/pulp


-include $(PULP_SDK_HOME)/install/rules/pulp.mk

header::
	mkdir -p $(PULP_SDK_HOME)/install/include/libgomp
	cp *.h $(PULP_SDK_HOME)/install/include/libgomp
	mkdir -p $(PULP_SDK_HOME)/install/include/libgomp/pulp/
	cp config/pulp/*.h $(PULP_SDK_HOME)/install/include/libgomp/pulp/
	mkdir -p $(PULP_SDK_HOME)/install/hero
	cp -r config/pulp/hero/refs/* $(PULP_SDK_HOME)/install/hero/

