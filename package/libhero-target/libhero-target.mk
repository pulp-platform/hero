################################################################################
#
# libhero-target
#
################################################################################

LIBHERO_TARGET_VERSION = 35ba09d378809080ae20e2131fc20320a900f0aa
LIBHERO_TARGET_SITE = $(call github,pulp-platform,libhero-target,$(LIBHERO_TARGET_VERSION))
LIBHERO_TARGET_LICENSE = Apache-2.0
LIBHERO_TARGET_LICENSE_FILES = LICENSE
LIBHERO_TARGET_INSTALL_STAGING = YES
LIBHERO_TARGET_INSTALL_TARGET = YES

# FIXME: find more reliable way to work with pulp-sdk from here
LIBHERO_TARGET_PULP_SDK_HOME = $(shell source $(BR2_EXTERNAL_HERO_PATH)/support/pulp-sdk/sourceme.sh > /dev/null 2>&1 && echo $$PULP_SDK_HOME)
LIBHERO_TARGET_MAKE_ENV = $(TARGET_MAKE_ENV) PATH=$(PATH):$(LIBHERO_TARGET_PULP_SDK_HOME)/install/ws/bin \
		LD_LIBRARY_PATH=$(LD_LIBRARY_PATH):$(PULP_SDK_HOME)/install/ws/lib \
		PULP_RISCV_GCC_TOOLCHAIN=$(RISCV) \
		CROSS_COMPILE=$(TARGET_CROSS)

define LIBHERO_TARGET_BUILD_CMDS
	(source $(BR2_EXTERNAL_HERO_PATH)/support/pulp-sdk/sourceme.sh; \
		cd $(@D); \
		$(LIBHERO_TARGET_MAKE_ENV) $(MAKE); \
	)
endef

define LIBHERO_TARGET_INSTALL_STAGING_CMDS
	$(INSTALL) -D -m 0644 $(@D)/inc/hero-target.h $(STAGING_DIR)/usr/include/hero-target.h
	$(INSTALL) -D -m 0755 $(@D)/lib/libhero-target.so $(STAGING_DIR)/usr/lib/libhero-target.so
	$(INSTALL) -D -m 0644 $(@D)/lib/libhero-target.a $(STAGING_DIR)/usr/lib/libhero-target.a
endef

define LIBHERO_TARGET_INSTALL_TARGET_CMDS
	$(INSTALL) -D -m 0755 $(@D)/lib/libhero-target.so $(TARGET_DIR)/usr/lib/libhero-target.so
endef

$(eval $(generic-package))
