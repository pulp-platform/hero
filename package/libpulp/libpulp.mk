################################################################################
#
# libpulp
#
################################################################################

LIBPULP_VERSION = 0.1
LIBPULP_SITE_METHOD = local
LIBPULP_SITE = $(BR2_EXTERNAL_HERO_PATH)/support/libpulp
LIBPULP_MODULE_SUBDIRS = pulp-driver
LIBPULP_INSTALL_STAGING = YES
LIBPULP_INSTALL_TARGET = YES

LIBPULP_APPS_DIR = $(BR2_EXTERNAL_HERO_PATH)/apps/

LIBPULP_PULP_INC = $(BR2_EXTERNAL_HERO_PATH)/pulp/sdk/pkg/sdk/dev/install/include/
LIBPULP_CFLAGS = -DDEBUG_LEVEL=$(BR2_PACKAGE_LIBPULP_DEBUG_LEVEL)
ifneq ($(BR2_PACKAGE_LIBPULP_DEBUG_LEVEL),0)
LIBPULP_CFLAGS += -g
endif

LIBPULP_MK_OPTS = PLATFORM=$(BR2_PACKAGE_HERO_PLATFORM) CFLAGS="$(LIBPULP_CFLAGS)"
LIBPULP_MODULE_MAKE_OPTS = $(LIBPULP_MK_OPTS)

LIBPULP_TARGET_MAKE_ENV = $(TARGET_MAKE_ENV) $(LIBPULP_MK_OPTS) \
	HERO_PULP_INC_DIR=$(LIBPULP_PULP_INC) \
	CROSS_COMPILE=$(TARGET_CROSS)

define LIBPULP_CLEAN_BUILD
	$(LIBPULP_TARGET_MAKE_ENV) $(MAKE1) -C $(@D) clean
endef
LIBPULP_PRE_BUILD_HOOKS += LIBPULP_CLEAN_BUILD

define LIBPULP_BUILD_CMDS
	$(LIBPULP_TARGET_MAKE_ENV) $(MAKE1) -C $(@D) build
endef

define LIBPULP_INSTALL_STAGING_CMDS
	$(INSTALL) -D -m 0644 $(@D)/inc/pulp.h $(STAGING_DIR)/usr/include/pulp.h
	$(INSTALL) -D -m 0644 $(@D)/inc/pulp_common.h $(STAGING_DIR)/usr/include/pulp_common.h
	$(INSTALL) -D -m 0755 $(@D)/lib/libpulp.so $(STAGING_DIR)/usr/lib/libpulp.so
	$(INSTALL) -D -m 0644 $(@D)/lib/libpulp.a $(STAGING_DIR)/usr/lib/libpulp.a
endef

define LIBPULP_INSTALL_TARGET_CMDS
	$(INSTALL) -D -m 0755 $(@D)/lib/libpulp.so $(TARGET_DIR)/usr/lib/libpulp.so
endef

$(eval $(generic-package))
