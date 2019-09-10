################################################################################
#
# ariane-support
#
################################################################################

# TODO: implement properly after app infrastructure is properly setup

ARIANE_SUPPORT_VERSION = 0.1
ARIANE_SUPPORT_SITE_METHOD = local
ARIANE_SUPPORT_SITE = $(BR2_EXTERNAL_HERO_PATH)/apps/ariane
ARIANE_SUPPORT_INSTALL_TARGET = YES

define ARIANE_SUPPORT_BUILD_CMDS
	$(TARGET_CC) $(@D)/addentropy.c -o $(@D)/addentropy
	$(TARGET_CC) $(@D)/cachetest.c -o $(@D)/cachetest
endef

ifeq ($(BR2_PACKAGE_ARIANE_SUPPORT_RANDOM_INIT),y)
define ARIANE_SUPPORT_INSTALL_TARGET_RANDOM_INIT
	dd if=/dev/urandom of=$(TARGET_DIR)/etc/random-seed count=512 status=none
	$(INSTALL) -D -m 0755 $(@D)/addentropy $(TARGET_DIR)/usr/bin/addentropy
endef
define ARIANE_SUPPORT_INSTALL_INIT_SYSV_RANDOM_INIT
	$(INSTALL) -D -m 0775 $(ARIANE_SUPPORT_PKGDIR)/S20urandom $(TARGET_DIR)/etc/init.d/
endef
endif

ifeq ($(call qstrip,$(BR2_PACKAGE_ARIANE_SUPPORT_EXT_MOUNT)),)
define ARIANE_SUPPORT_INSTALL_INIT_SYSV_ETH_MAC
	$(INSTALL) -D -m 0775 $(ARIANE_SUPPORT_PKGDIR)/S30ethfix $(TARGET_DIR)/etc/init.d/
endef
else
define ARIANE_SUPPORT_INSTALL_INIT_SYSV_ETH_MAC
	$(INSTALL) -D -m 0775 $(ARIANE_SUPPORT_PKGDIR)/S30ethfix $(TARGET_DIR)/etc/init.d/
	$(SED) 's/00:18:3e:02:e3:7f/$(call qstrip,$(BR2_PACKAGE_ARIANE_SUPPORT_ETH_MAC))/' $(TARGET_DIR)/etc/init.d/S30ethfix
endef
endif

ifneq ($(call qstrip,$(BR2_PACKAGE_ARIANE_SUPPORT_EXT_MOUNT)),)
define ARIANE_SUPPORT_INSTALL_INIT_SYSV_EXT_MOUNT
	$(INSTALL) -D -m 755 $(ARIANE_SUPPORT_PKGDIR)/S99extroot $(TARGET_DIR)/etc/init.d/S99extroot
	$(SED) 's|EXTERNAL_MOUNT_POINT|$(call qstrip,$(BR2_PACKAGE_ARIANE_SUPPORT_EXT_MOUNT))|' $(TARGET_DIR)/etc/init.d/S99extroot
endef
endif

define ARIANE_SUPPORT_INSTALL_TARGET_CMDS
	$(ARIANE_SUPPORT_INSTALL_TARGET_RANDOM_INIT)
	$(INSTALL) -D -m 0755 $(@D)/cachetest $(TARGET_DIR)/usr/local/bin/cachetest
endef

define ARIANE_SUPPORT_INSTALL_INIT_SYSV
	$(ARIANE_SUPPORT_INSTALL_INIT_SYSV_RANDOM_INIT)
	$(ARIANE_SUPPORT_INSTALL_INIT_SYSV_ETH_MAC)
	$(ARIANE_SUPPORT_INSTALL_INIT_SYSV_EXT_MOUNT)
endef

$(eval $(generic-package))
