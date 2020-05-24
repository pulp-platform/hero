################################################################################
#
# libhero-target
#
################################################################################

LIBHERO_TARGET_VERSION = 0.1
LIBHERO_TARGET_SITE_METHOD = local
LIBHERO_TARGET_SITE = $(BR2_EXTERNAL_HERO_PATH)/support/libhero-target
LIBHERO_TARGET_LICENSE = Apache-2.0
LIBHERO_TARGET_LICENSE_FILES = LICENSE
LIBHERO_TARGET_INSTALL_STAGING = YES
LIBHERO_TARGET_INSTALL_TARGET = YES

LIBHERO_TARGET_MAKE_ENV = $(TARGET_MAKE_ENV) CROSS_COMPILE=$(TARGET_CROSS)

define LIBHERO_TARGET_BUILD_CMDS
	cd $(@D)/host/ && $(LIBHERO_TARGET_MAKE_ENV) $(MAKE) clean
	cd $(@D)/host/ && $(LIBHERO_TARGET_MAKE_ENV) $(MAKE) build
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
