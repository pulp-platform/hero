################################################################################
#
# hero-support
#
################################################################################

HERO_APPS_VERSION = 0.1
HERO_APPS_SITE_METHOD = local
HERO_APPS_SITE = $(BR2_EXTERNAL_HERO_PATH)/apps/hero-snitch
HERO_APPS_INSTALL_TARGET = YES
HERO_APPS_DEPENDENCIES = libsnitch

HERO_APPS_MK_OPTS = PLATFORM=$(BR2_PACKAGE_HERO_PLATFORM)

HERO_APPS_TARGET_MAKE_ENV = $(TARGET_MAKE_ENV) $(HERO_APPS_MK_OPTS) \
	CROSS_COMPILE=$(TARGET_CROSS)

define HERO_APPS_CLEAN_BUILD
	$(HERO_APPS_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/standalone clean
endef
HERO_APPS_PRE_BUILD_HOOKS += HERO_APPS_CLEAN_BUILD

define HERO_APPS_BUILD_CMDS
	$(HERO_APPS_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/standalone build
endef

define HERO_APPS_INSTALL_TARGET_CMDS
	$(INSTALL) -D -m 0755 $(@D)/standalone/standalone $(TARGET_DIR)/usr/bin/standalone-snitch
endef

$(eval $(generic-package))
