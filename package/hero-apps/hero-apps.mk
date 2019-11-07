################################################################################
#
# hero-support
#
################################################################################

HERO_APPS_VERSION = 0.1
HERO_APPS_SITE_METHOD = local
HERO_APPS_SITE = $(BR2_EXTERNAL_HERO_PATH)/apps/hero
HERO_APPS_INSTALL_TARGET = YES
HERO_APPS_DEPENDENCIES = libpulp

HERO_APPS_PULP_INC = $(BR2_EXTERNAL_HERO_PATH)/pulp/sdk/pkg/sdk/dev/install/include/

HERO_APPS_MK_OPTS = PLATFORM=$(BR2_PACKAGE_HERO_PLATFORM)

HERO_APPS_TARGET_MAKE_ENV = $(TARGET_MAKE_ENV) $(HERO_APPS_MK_OPTS) \
	HERO_PULP_INC_DIR=$(HERO_APPS_PULP_INC) \
	HERO_LIBPULP_DIR=${LIBPULP_SITE} \
	CROSS_COMPILE=$(TARGET_CROSS)

define HERO_APPS_CLEAN_BUILD
	$(HERO_APPS_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/standalone clean
	$(HERO_APPS_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/uart clean
endef
HERO_APPS_PRE_BUILD_HOOKS += HERO_APPS_CLEAN_BUILD

define HERO_APPS_BUILD_CMDS
	$(HERO_APPS_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/standalone build
	$(HERO_APPS_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/uart build
endef

define HERO_APPS_INSTALL_TARGET_CMDS
	$(INSTALL) -D -m 0755 $(@D)/standalone/standalone $(TARGET_DIR)/usr/bin/pulp-standalone
	$(INSTALL) -D -m 0755 $(@D)/uart/uart $(TARGET_DIR)/usr/bin/pulp-uart
endef

$(eval $(generic-package))
