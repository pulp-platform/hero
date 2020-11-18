ARCHI_HOST_FILES = $(shell plpfiles copy --item=archi_host_files)

INSTALL_FILES += $(foreach file,$(ARCHI_HOST_FILES),include/$(file))

WS_INSTALL_FILES += $(INSTALL_FILES)

PULP_LIBS = archi_host

PULP_LIB_CL_SRCS_archi_host = $(shell plpfiles copy --item=archi_host_src_files)

debug:
	echo $(ARCHI_HOST_FILES)

include $(PULP_SDK_HOME)/install/rules/pulp_rt.mk
