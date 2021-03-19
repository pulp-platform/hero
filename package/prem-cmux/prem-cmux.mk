################################################################################
#
# prem-cmux
#
################################################################################

PREM_CMUX_VERSION = 0.1
PREM_CMUX_SITE_METHOD = local
PREM_CMUX_SITE = $(BR2_EXTERNAL_HERO_PATH)/toolchain/HerculesCompiler-public/runtime/cmux
PREM_CMUX_INSTALL_STAGING = YES
PREM_CMUX_INSTALL_TARGET = YES

PREM_CMUX_MAKE_ENV = $(TARGET_MAKE_ENV) CROSS_COMPILE=$(TARGET_CROSS)

define PREM_CMUX_BUILD_CMDS
	$(PREM_CMUX_MAKE_ENV) $(MAKE) -C $(PREM_CMUX_SITE) cmux
endef

define PREM_CMUX_INSTALL_STAGING_CMDS
	$(INSTALL) -D -m 0755 $(PREM_CMUX_SITE)/bin/cmux $(STAGING_DIR)/usr/bin/cmux
	$(INSTALL) -D -m 0644 $(PREM_CMUX_SITE)/lib/libcmux-vote.a $(STAGING_DIR)/usr/lib/libcmux-vote.a
	$(INSTALL) -D -m 0644 $(PREM_CMUX_SITE)/lib/libpremnotify-cpu.so $(STAGING_DIR)/usr/lib/libpremnotify.so
	mkdir -p $(STAGING_DIR)/usr/include/prem
	$(INSTALL) -D -m 0644 $(PREM_CMUX_SITE)/inc/prem/cmuxif.h $(STAGING_DIR)/usr/include/prem/cmuxif.h
	$(INSTALL) -D -m 0644 $(PREM_CMUX_SITE)/inc/prem/vote.h $(STAGING_DIR)/usr/include/prem/vote.h
	$(INSTALL) -D -m 0644 $(PREM_CMUX_SITE)/inc/prem/libpremnotify.h $(STAGING_DIR)/usr/include/prem/libpremnotify.h
	$(INSTALL) -D -m 0644 $(PREM_CMUX_SITE)/inc/prem/channel.h $(STAGING_DIR)/usr/include/prem/channel.h
	$(INSTALL) -D -m 0644 $(PREM_CMUX_SITE)/inc/prem/logprint.h $(STAGING_DIR)/usr/include/prem/logprint.h
endef

define PREM_CMUX_INSTALL_TARGET_CMDS
	$(INSTALL) -D -m 0755 $(STAGING_DIR)/usr/bin/cmux $(TARGET_DIR)/usr/bin/cmux
	$(INSTALL) -D -m 0644 $(STAGING_DIR)/usr/lib/libcmux-vote.a $(TARGET_DIR)/usr/lib/libcmux-vote.a
	$(INSTALL) -D -m 0644 $(STAGING_DIR)/usr/lib/libpremnotify.so $(TARGET_DIR)/usr/lib/libpremnotify.so
	mkdir -p $(TARGET_DIR)/usr/include/prem
	$(INSTALL) -D -m 0644 $(STAGING_DIR)/usr/include/prem/cmuxif.h $(TARGET_DIR)/usr/include/prem/cmuxif.h
	$(INSTALL) -D -m 0644 $(STAGING_DIR)/usr/include/prem/vote.h $(TARGET_DIR)/usr/include/prem/vote.h
	$(INSTALL) -D -m 0644 $(STAGING_DIR)/usr/include/prem/libpremnotify.h $(TARGET_DIR)/usr/include/prem/libpremnotify.h
	$(INSTALL) -D -m 0644 $(STAGING_DIR)/usr/include/prem/channel.h $(TARGET_DIR)/usr/include/prem/channel.h
	$(INSTALL) -D -m 0644 $(STAGING_DIR)/usr/include/prem/logprint.h $(TARGET_DIR)/usr/include/prem/logprint.h
endef

$(eval $(generic-package))
