################################################################################
#
# libsnitch
#
################################################################################

LIBSNITCH_VERSION = 0.1
LIBSNITCH_SITE_METHOD = local
LIBSNITCH_SITE = $(BR2_EXTERNAL_HERO_PATH)/support/libsnitch
LIBSNITCH_MODULE_SUBDIRS = snitch-driver
LIBSNITCH_INSTALL_STAGING = YES
LIBSNITCH_INSTALL_TARGET = YES

LIBSNITCH_CFLAGS = -DDEBUG_LEVEL=$(BR2_PACKAGE_LIBSNITCH_DEBUG_LEVEL)
LIBSNITCH_CFLAGS += -DPLATFORM=$(BR2_PACKAGE_HERO_PLATFORM)
ifneq ($(BR2_PACKAGE_LIBSNITCH_DEBUG_LEVEL),0)
LIBSNITCH_CFLAGS += -g
endif

LIBSNITCH_EXTERNAL_INC_PATHS = $(BR2_EXTERNAL_HERO_PATH)/support/include $(BR2_EXTERNAL_HERO_PATH)/support/snitch-driver

LIBSNITCH_MK_OPTS = PLATFORM=$(BR2_PACKAGE_HERO_PLATFORM) CFLAGS="$(LIBSNITCH_CFLAGS)"
LIBSNITCH_MODULE_MAKE_OPTS = $(LIBSNITCH_MK_OPTS)

LIBSNITCH_TARGET_MAKE_ENV = $(TARGET_MAKE_ENV) $(LIBSNITCH_MK_OPTS) \
	CROSS_COMPILE=$(TARGET_CROSS) \
  INC_DIRS="$(LIBSNITCH_EXTERNAL_INC_PATHS)"

define LIBSNITCH_CLEAN_BUILD
	$(LIBSNITCH_TARGET_MAKE_ENV) $(MAKE1) -C $(@D) clean
endef
LIBSNITCH_PRE_BUILD_HOOKS += LIBSNITCH_CLEAN_BUILD

define LIBSNITCH_BUILD_CMDS
	$(LIBSNITCH_TARGET_MAKE_ENV) $(MAKE1) -C $(@D) build
endef

define LIBSNITCH_INSTALL_STAGING_CMDS
	$(INSTALL) -D -m 0644 $(@D)/include/fesrv.h $(STAGING_DIR)/usr/include/fesrv.h
	$(INSTALL) -D -m 0644 $(@D)/include/libsnitch.h $(STAGING_DIR)/usr/include/libsnitch.h
	$(INSTALL) -D -m 0755 $(@D)/lib/libsnitch.so $(STAGING_DIR)/usr/lib/libsnitch.so
	$(INSTALL) -D -m 0644 $(@D)/lib/libsnitch.a $(STAGING_DIR)/usr/lib/libsnitch.a
endef

define LIBSNITCH_INSTALL_TARGET_CMDS
	$(INSTALL) -D -m 0755 $(@D)/lib/libsnitch.so $(TARGET_DIR)/usr/lib/libsnitch.so
endef

$(eval $(generic-package))
