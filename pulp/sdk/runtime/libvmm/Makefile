LIBVMM_FILES = $(shell plpfiles copy --item=libvmm_files)

INSTALL_FILES += $(foreach file,$(LIBVMM_FILES),include/$(file))

WS_INSTALL_FILES += $(INSTALL_FILES)

PULP_LIBS = vmm

PULP_LIB_CL_SRCS_vmm = $(shell plpfiles copy --item=libvmm_src_files)

debug:
	echo $(LIBVMM_FILES)

include $(PULP_SDK_HOME)/install/rules/pulp.mk
