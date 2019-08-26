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

LIBHERO_TARGET_MAKE_ENV = $(TARGET_MAKE_ENV) CROSS_COMPILE=$(TARGET_CROSS)

# FIXME: find more reliable way to work with pulp-sdk from here
LIBHERO_TARGET_PULP_SDK_HOME = $(shell source $(BR2_EXTERNAL_HERO_PATH)/support/pulp-sdk/sourceme.sh > /dev/null 2>&1 && echo $$PULP_SDK_HOME)
LIBHERO_ACCEL_MAKE_ENV = PATH=$(PATH):$(LIBHERO_TARGET_PULP_SDK_HOME)/install/ws/bin \
		LD_LIBRARY_PATH=$(LD_LIBRARY_PATH):$(PULP_SDK_HOME)/install/ws/lib \
		PULP_RISCV_GCC_TOOLCHAIN=$(RISCV) \

define LIBHERO_TARGET_BUILD_CMDS
	cd $(@D)/host/ && $(LIBHERO_TARGET_MAKE_ENV) $(MAKE) build
endef

define LIBHERO_TARGET_BUILD_ACCEL_CMDS
	(source $(BR2_EXTERNAL_HERO_PATH)/support/pulp-sdk/sourceme.sh; \
		cd $(@D)/pulp; \
		$(LIBHERO_ACCEL_MAKE_ENV) $(MAKE) header build; \
	)
endef
LIBHERO_TARGET_POST_BUILD_HOOKS += LIBHERO_TARGET_BUILD_ACCEL_CMDS

define LIBHERO_TARGET_INSTALL_STAGING_CMDS
	$(INSTALL) -D -m 0644 $(@D)/inc/hero-target.h $(STAGING_DIR)/usr/include/hero-target.h
	$(INSTALL) -D -m 0755 $(@D)/lib/libhero-target.so $(STAGING_DIR)/usr/lib/libhero-target.so
	$(INSTALL) -D -m 0644 $(@D)/lib/libhero-target.a $(STAGING_DIR)/usr/lib/libhero-target.a
endef

define LIBHERO_TARGET_INSTALL_TARGET_CMDS
	$(INSTALL) -D -m 0755 $(@D)/lib/libhero-target.so $(TARGET_DIR)/usr/lib/libhero-target.so
endef

define LIBHERO_TARGET_INSTALL_ACCEL_CMDS
	(source $(BR2_EXTERNAL_HERO_PATH)/support/pulp-sdk/sourceme.sh; \
		cd $(@D)/pulp; \
		$(LIBHERO_TARGET_MAKE_ENV) $(MAKE) install; \
	)
endef
LIBHERO_TARGET_POST_INSTALL_TARGET_HOOKS += LIBHERO_TARGET_INSTALL_ACCEL_CMDS

$(eval $(generic-package))
