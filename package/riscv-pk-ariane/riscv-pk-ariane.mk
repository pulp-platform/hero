################################################################################
#
# riscv-pk-ariane
#
################################################################################

RISCV_PK_ARIANE_VERSION = bfcbacb13fd9f70fb21a4c129e2be0d5e78be977
RISCV_PK_ARIANE_SITE = $(call github,pulp-platform,riscv-pk,$(RISCV_PK_ARIANE_VERSION))
RISCV_PK_ARIANE_LICENSE = BSD-3-Clause
RISCV_PK_ARIANE_LICENSE_FILES = LICENSE
RISCV_PK_ARIANE_DEPENDENCIES = linux
RISCV_PK_ARIANE_SUBDIR = build
RISCV_PK_ARIANE_INSTALL_IMAGES = YES

define RISCV_PK_ARIANE_CONFIGURE_CMDS
	mkdir -p $(RISCV_PK_ARIANE_DIR)/build
	(cd $(RISCV_PK_ARIANE_DIR)/build; \
		$(TARGET_CONFIGURE_OPTS) ../configure \
		--host=$(GNU_TARGET_NAME) \
		--with-payload=$(BINARIES_DIR)/vmlinux \
		$(call qstrip,$(BR2_PACKAGE_RISCV_PK_ARIANE_EXTRA_CONFIG_OPTS)) \
	)
endef

define RISCV_PK_ARIANE_BUILD_CMDS
	$(TARGET_MAKE_ENV) $(MAKE) -C $(RISCV_PK_ARIANE_DIR)/build bbl
endef

define RISCV_PK_ARIANE_INSTALL_IMAGES_CMDS
	$(INSTALL) -D -m 0755 $(RISCV_PK_ARIANE_DIR)/build/bbl $(BINARIES_DIR)/bbl
endef

$(eval $(generic-package))
