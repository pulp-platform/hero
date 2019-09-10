PULP_PROPERTIES += pulp_chip
include $(PULP_SDK_HOME)/install/rules/pulp_properties.mk

PULP_LIBS                  = hero-target
PULP_LIB_CL_SRCS_hero-target += hero-target.c
PULP_CL_CFLAGS_hero-target    = -Wall -O3 -g3 -I../inc

-include $(PULP_SDK_HOME)/install/rules/pulp.mk

header::
	mkdir -p $(PULP_SDK_HOME)/install/include/libhero-target
	cp ../inc/hero-target.h $(PULP_SDK_HOME)/install/include/libhero-target
