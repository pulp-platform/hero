#############################################################################
#
# zynq fclkcfg
#
################################################################################

ZYNQ_FCLKCFG_VERSION = 4c248474482223af0ea8dd8de15e08928ffeb40e
ZYNQ_FCLKCFG_SITE = $(call github,ikwzm,fclkcfg,$(ZYNQ_FCLKCFG_VERSION))
ZYNQ_FCLKCFG_LICENSE = BSD-2-Clause
ZYNQ_FCLKCFG_LICENSE_FILES = LICENSE
ZYNQ_FCLKCFG_INSTALL_TARGET = YES

$(eval $(kernel-module))
$(eval $(generic-package))
