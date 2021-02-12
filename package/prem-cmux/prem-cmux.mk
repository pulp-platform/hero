################################################################################
#
# prem-cmux
#
################################################################################

PREM_CMUX_VERSION = 0.1
PREM_CMUX_SITE_METHOD = local
PREM_CMUX_SITE = $(BR2_EXTERNAL_HERO_PATH)/cmux
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
  # TODO We should move all of these headers to the prem subdirectory to keep them organized
	mkdir -p $(STAGING_DIR)/usr/include/prem
	$(INSTALL) -D -m 0644 $(PREM_CMUX_SITE)/inc/cmuxif.h $(STAGING_DIR)/usr/include/prem/cmuxif.h
	$(INSTALL) -D -m 0644 $(PREM_CMUX_SITE)/inc/vote.h $(STAGING_DIR)/usr/include/prem/vote.h
	$(INSTALL) -D -m 0644 $(PREM_CMUX_SITE)/inc/vote.h $(STAGING_DIR)/usr/include/vote.h
	$(INSTALL) -D -m 0644 $(PREM_CMUX_SITE)/inc/libpremnotify.h $(STAGING_DIR)/usr/include/libpremnotify.h
	$(INSTALL) -D -m 0644 $(PREM_CMUX_SITE)/inc/channel.h $(STAGING_DIR)/usr/include/channel.h
	$(INSTALL) -D -m 0644 $(PREM_CMUX_SITE)/inc/logprint.h $(STAGING_DIR)/usr/include/logprint.h
endef

$(eval $(generic-package))
