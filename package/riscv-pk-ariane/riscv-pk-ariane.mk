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
RISCV_PK_ARIANE_INSTALL_IMAGES = YES

RISCV_PK_ARIANE_EXTRA_OPTS =
ifneq ($(call qstrip,$(BR2_PACKAGE_RISCV_PK_ARIANE_LOGO)),)
  RISCV_PK_ARIANE_EXTRA_OPTS += --enable-logo --with-logo=$(BR2_PACKAGE_RISCV_PK_ARIANE_LOGO)
endif

define RISCV_PK_ARIANE_CONFIGURE
  rm -rf $(RISCV_PK_ARIANE_DIR)/build
	mkdir -p $(RISCV_PK_ARIANE_DIR)/build
	(cd $(RISCV_PK_ARIANE_DIR)/build; \
		$(TARGET_CONFIGURE_OPTS) ../configure \
		--host=$(GNU_TARGET_NAME) \
		--with-payload=$(BINARIES_DIR)/vmlinux \
		$(RISCV_PK_ARIANE_EXTRA_OPTS) \
	)
endef

define RISCV_PK_ARIANE_CONFIGURE_CMDS
endef
define RISCV_PK_ARIANE_BUILD_CMDS
	@echo "Completing build after final Linux image is created"
endef
define RISCV_PK_ARIANE_INSTALL_IMAGES_CMDS
endef

define RISCV_PK_ARIANE_BUILD
	$(TARGET_MAKE_ENV) $(MAKE) -C $(RISCV_PK_ARIANE_DIR)/build bbl
endef

# Note this trick to add it to the RootFS targets will make sure the bbl is created last
rootfs-riscv-pk-ariane: linux-rebuild-with-initramfs
	$(RISCV_PK_ARIANE_CONFIGURE)
	$(RISCV_PK_ARIANE_BUILD)
	$(INSTALL) -D -m 0755 $(RISCV_PK_ARIANE_DIR)/build/bbl $(BINARIES_DIR)/bbl

.PHONY: rootfs-riscv_pk_ariane
ifeq (${BR2_PACKAGE_RISCV_PK_ARIANE},y)
TARGETS_ROOTFS += rootfs-riscv-pk-ariane
endif

$(eval $(generic-package))
