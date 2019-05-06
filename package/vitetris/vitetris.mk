################################################################################
#
# vitetris
#
################################################################################

VITETRIS_VERSION = 1de427e2b7044c55401b18ee6b32390c9abb0e7c
VITETRIS_SITE = $(call github,vicgeralds,vitetris,$(VITETRIS_VERSION))
VITETRIS_LICENSE = BSD-2-Clause
VITETRIS_LICENSE_FILES = license.txt
VITETRIS_INSTALL_TARGET_OPTS = INSTALL=install DESTDIR=$(TARGET_DIR) install
VITETRIS_INSTALL_TARGET = YES

define VITETRIS_CONFIGURE_CMDS
	$(TARGET_CONFIGURE_OPTS) $(TARGET_CONFIGURE_ARGS) $(@D)/configure --prefix=/usr/local --disable-x --disable-js --disable-2p
endef

# NOTE: not an actual autotools package but similar behavior
$(eval $(autotools-package))
