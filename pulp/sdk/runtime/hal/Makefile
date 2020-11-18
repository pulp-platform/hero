HAL_FILES = $(shell plpfiles copy --item=hal_files)

HAL_SRC_FILES = $(shell plpfiles copy --item=hal_src_files)

HAL_FILES += hal/pulp.h hal/utils.h hal/pulp_io.h hal/debug_bridge/debug_bridge.h

WS_INSTALL_FILES += $(foreach file,$(HAL_FILES),include/$(file))

INSTALL_FILES += $(WS_INSTALL_FILES)

INSTALL_FILES += $(foreach file,$(HAL_SRC_FILES),src/$(file))

include $(PULP_SDK_HOME)/install/rules/pulp.mk
