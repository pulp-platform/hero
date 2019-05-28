################################################################################
#
# hero-support
#
################################################################################

HERO_SUPPORT_VERSION = 84f2bec5f4437e748cf9be020b1b409896d184f9
HERO_SUPPORT_SITE = $(call github,pulp-platform,hero-support,$(HERO_SUPPORT_VERSION))
HERO_SUPPORT_MODULE_SUBDIRS = drivers/pulp
HERO_SUPPORT_INSTALL_STAGING = YES
HERO_SUPPORT_INSTALL_TARGET = YES

HERO_SUPPORT_PULP_INC = $(BR2_EXTERNAL_HERO_PATH)/support/pulp-sdk/pkg/sdk/dev/install/include/
HERO_SUPPORT_CFLAGS = -DDEBUG_LEVEL=$(BR2_PACKAGE_HERO_SUPPORT_DEBUG_LEVEL)
ifneq ($(BR2_PACKAGE_HERO_SUPPORT_DEBUG_LEVEL),0)
HERO_SUPPORT_CFLAGS += -g
endif

HERO_SUPPORT_PLATFORM = ARIANE
HERO_SUPPORT_MK_OPTS = PLATFORM=$(HERO_SUPPORT_PLATFORM) CFLAGS="$(HERO_SUPPORT_CFLAGS)"
HERO_SUPPORT_MODULE_MAKE_OPTS = $(HERO_SUPPORT_MK_OPTS)

HERO_SUPPORT_TARGET_MAKE_ENV = $(TARGET_MAKE_ENV) $(HERO_SUPPORT_MK_OPTS) \
	HERO_PULP_INC_DIR=$(HERO_SUPPORT_PULP_INC) \
	HERO_LIBPULP_DIR=$(@D)/libpulp \
	KERNEL_ARCH=$(KERNEL_ARCH) \
	KERNEL_DIR=$(LINUX_DIR) \
	KERNEL_CROSS_COMPILE=$(TARGET_CROSS) \
	CROSS_COMPILE=$(TARGET_CROSS)

define HERO_SUPPORT_CLEAN_BUILD
	$(HERO_SUPPORT_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/libpulp clean
	$(HERO_SUPPORT_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/drivers/pulp clean
	$(HERO_SUPPORT_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/apps/standalone clean
	$(HERO_SUPPORT_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/apps/uart clean
endef
HERO_SUPPORT_PRE_BUILD_HOOKS += HERO_SUPPORT_CLEAN_BUILD

define HERO_SUPPORT_BUILD_CMDS
	$(HERO_SUPPORT_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/libpulp build
	$(HERO_SUPPORT_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/drivers/pulp build
endef

define HERO_SUPPORT_BUILD_APPS
  $(HERO_SUPPORT_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/apps/standalone build
	$(HERO_SUPPORT_TARGET_MAKE_ENV) $(MAKE) -C $(@D)/apps/uart build
endef
HERO_SUPPORT_POST_BUILD_HOOKS += HERO_SUPPORT_BUILD_APPS

define HERO_SUPPORT_INSTALL_STAGING_CMDS
	$(INSTALL) -D -m 0644 $(@D)/libpulp/inc/pulp.h $(STAGING_DIR)/usr/local/include/pulp.h
	$(INSTALL) -D -m 0755 $(@D)/libpulp/lib/libpulp.so $(STAGING_DIR)/usr/local/lib/libpulp.so
	$(INSTALL) -D -m 0644 $(@D)/libpulp/lib/libpulp.a $(STAGING_DIR)/usr/local/lib/libpulp.a
endef

define HERO_SUPPORT_INSTALL_TARGET_CMDS
	$(INSTALL) -D -m 0755 $(@D)/libpulp/lib/libpulp.so $(TARGET_DIR)/usr/local/lib/libpulp.so
	$(INSTALL) -D -m 0755 $(@D)/apps/standalone/standalone $(TARGET_DIR)/usr/local/bin/pulp-standalone
	$(INSTALL) -D -m 0755 $(@D)/apps/uart/uart $(TARGET_DIR)/usr/local/bin/pulp-uart
endef

$(eval $(generic-package))
