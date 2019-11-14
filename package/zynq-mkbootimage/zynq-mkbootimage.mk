################################################################################
#
# zynq mkbootimage
#
################################################################################

ZYNQ_MKBOOTIMAGE_VERSION = 4ee42d782a9ba65725ed165a4916853224a8edf7
ZYNQ_MKBOOTIMAGE_SITE = $(call github,antmicro,zynq-mkbootimage,$(ZYNQ_MKBOOTIMAGE_VERSION))
ZYNQ_MKBOOTIMAGE_LICENSE = BSD-2-Clause
ZYNQ_MKBOOTIMAGE_LICENSE_FILES = LICENSE
ZYNQ_MKBOOTIMAGE_INSTALL_TARGET = YES
HOST_ZYNQ_MKBOOTIMAGE_DEPENDENCIES = host-pcre host-elfutils

define HOST_ZYNQ_MKBOOTIMAGE_BUILD_CMDS
    $(HOST_MAKE_ENV) $(HOST_CONFIGURE_OPTS) $(MAKE) -C $(@D)
endef

define HOST_ZYNQ_MKBOOTIMAGE_INSTALL_CMDS
    $(INSTALL) -D -m 0755 $(@D)/mkbootimage $(HOST_DIR)/bin
endef

$(eval $(host-generic-package))
