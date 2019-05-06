################################################################################
#
# ariane-support
#
################################################################################

# TODO: implement properly after app infrastructure is properly setup

ARIANE_SUPPORT_VERSION = 0.1
ARIANE_SUPPORT_SITE_METHOD = local
ARIANE_SUPPORT_SITE = $(BR2_EXTERNAL_HERO_PATH)/apps/ariane-support
ARIANE_SUPPORT_INSTALL_TARGET = YES

define ARIANE_SUPPORT_BUILD_CMDS
	$(TARGET_CC) $(@D)/addentropy.c -o $(@D)/addentropy
	$(TARGET_CC) $(@D)/cachetest.c -o $(@D)/cachetest
endef

define ARIANE_SUPPORT_INSTALL_TARGET_CMDS
	$(INSTALL) -D -m 0755 $(@D)/addentropy $(TARGET_DIR)/usr/local/bin/addentropy
	$(INSTALL) -D -m 0755 $(@D)/cachetest $(TARGET_DIR)/usr/local/bin/cachetest
endef


define ARIANE_SUPPORT_INSTALL_INIT_SYSV
  if [ -z $(BR2_PACKAGE_ARIANE_SUPPORT_ETH_MAC) ]; then \
		$(INSTALL) -D -m 0775 $(ARIANE_SUPPORT_PKGDIR)/S30ethfix $(TARGET_DIR)/etc/init.d/; \
	else \
		cat $(ARIANE_SUPPORT_PKGDIR)/S30ethfix | sed 's/00:18:3e:02:e3:7f/$(call qstrip,$(BR2_PACKAGE_ARIANE_SUPPORT_ETH_MAC))/' > $(TARGET_DIR)/etc/init.d/S30ethfix; \
		chmod 755 $(TARGET_DIR)/etc/init.d/S30ethfix; \
	fi
	if [ ! -z $(BR2_PACKAGE_ARIANE_SUPPORT_EXT_MOUNT) ]; then \
		cat $(ARIANE_SUPPORT_PKGDIR)/S99extroot | sed 's|EXTERNAL_MOUNT_POINT|$(call qstrip,$(BR2_PACKAGE_ARIANE_SUPPORT_EXT_MOUNT))|' > $(TARGET_DIR)/etc/init.d/S99extroot; \
		chmod 755 $(TARGET_DIR)/etc/init.d/S99extroot; \
	fi

endef

$(eval $(generic-package))
