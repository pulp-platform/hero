################################################################################
#
# prem-cmux
#
################################################################################

PREM_CMUX_VERSION = 0.1
PREM_CMUX_SITE_METHOD = local
PREM_CMUX_SITE = $(BR2_EXTERNAL_HERO_PATH)/cmux
PREM_CMUX_LICENSE = Apache-2.0
PREM_CMUX_LICENSE_FILES = LICENSE
PREM_CMUX_INSTALL_STAGING = YES
PREM_CMUX_INSTALL_TARGET = YES

PREM_CMUX_MAKE_ENV = $(TARGET_MAKE_ENV) CROSS_COMPILE=$(TARGET_CROSS)

$(warning HELLO WORLD)

define PREM_CMUX_BUILD_CMDS
	$(PREM_CMUX_MAKE_ENV) $(MAKE) cmux
endef

define PREM_CMUX_INSTALL_STAGING_CMDS
	$(INSTALL) -D -m 0755 $(@D)/bin/cmux $(STAGING_DIR)/usr/bin/cmux
	$(INSTALL) -D -m 0644 $(@D)/lib/libcmux.a $(STAGING_DIR)/usr/lib/libcmux.a
	$(INSTALL) -D -m 0644 $(@D)/lib/libpremnotify-cpu.so $(STAGING_DIR)/usr/lib/libpremnotify.so
endef

$(eval $(generic-package))
