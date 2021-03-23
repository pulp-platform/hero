ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

PREM_BR_CMUX_CONFSTR := BR2_PACKAGE_PREM_CMUX=y
PREM_BR_OMP_CONFSTR := BR2_PACKAGE_HERO_OPENMP_ENABLE_PREM=y

# GLOBAL TARGETS
.PHONY: har-exilzcu102 hrv-ediggenesys2
har-exilzcu102: tc-har-olinux tc-pulp br-har-exilzcu102 sdk-pulp sdk-har tc-llvm
hrv-ediggenesys2: tc-hrv-olinux tc-pulp br-hrv-ediggenesys2 sdk-pulp sdk-hrv tc-llvm

# BUILDROOT
.PHONY: br-hrv-ediggenesys2-base br-hrv-ediggenesys2 br-har-exilzcu102-base br-har-exilzcu102 br-hrv br-har br-hrv-eqemu-base br-hrv-eqemu

# PREM configuration
.PHONY: prem-set prem-unset
prem-set:
	# Remove if already exists
	if [ -a $(CURDIR)/local.cfg ]; then grep -v "$(PREM_BR_CMUX_CONFSTR)" local.cfg > local.tmp.cfg; mv local.tmp.cfg local.cfg; fi
	if [ -a $(CURDIR)/local.cfg ]; then grep -v "$(PREM_BR_OMP_CONFSTR)" local.cfg > local.tmp.cfg; mv local.tmp.cfg local.cfg; fi
	# Re-add
	echo "$(PREM_BR_CMUX_CONFSTR)" >> $(CURDIR)/local.cfg
	echo "$(PREM_BR_OMP_CONFSTR)" >> $(CURDIR)/local.cfg

prem-unset:
	# Remove local buildroot config lines if they exist
	if [ -a $(CURDIR)/local.cfg ]; then grep -v "$(PREM_BR_CMUX_CONFSTR)" local.cfg > local.tmp.cfg; mv local.tmp.cfg local.cfg; fi
	if [ -a $(CURDIR)/local.cfg ]; then grep -v "$(PREM_BR_OMP_CONFSTR)" local.cfg > local.tmp.cfg; mv local.tmp.cfg local.cfg; fi

# environment
br-hrv-ediggenesys2-base: check_environment
	mkdir -p $(CURDIR)/output/br-hrv-ediggenesys2
	$(MAKE) O=$(CURDIR)/output/br-hrv-ediggenesys2 BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot hrv_ediggenesys2_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-hrv-ediggenesys2/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-hrv-ediggenesys2
	cp $(CURDIR)/output/br-hrv-ediggenesys2/images/bbl.bin $(CURDIR)/output/hrv-ediggenesys-base-bbl.bin
br-hrv-ediggenesys2: br-hrv-ediggenesys2-base

br-har-exilzcu102-base: check_environment
	mkdir -p $(CURDIR)/output/br-har-exilzcu102
	$(MAKE) O=$(CURDIR)/output/br-har-exilzcu102 BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot har_exilzcu102_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-har-exilzcu102/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-har-exilzcu102
	cp $(CURDIR)/output/br-har-exilzcu102/images/sdcard.img $(CURDIR)/output/har-exilzcu102-base-sdcard.img
br-har-exilzcu102: br-har-exilzcu102-base

# sdk images
br-hrv: check_environment
	mkdir -p $(CURDIR)/output/br-hrv
	$(MAKE) O=$(CURDIR)/output/br-hrv BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot hrv_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-hrv/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-hrv
	cp $(CURDIR)/output/br-hrv/images/rootfs.ext4 $(CURDIR)/output/hrv-rootfs.ext4
	cp $(CURDIR)/output/br-hrv/images/rootfs.tar $(CURDIR)/output/hrv-rootfs.tar

br-har: check_environment
	mkdir -p $(CURDIR)/output/br-har
	$(MAKE) O=$(CURDIR)/output/br-har BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot har_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-har/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-har
	cp $(CURDIR)/output/br-har/images/rootfs.ext4 $(CURDIR)/output/har-rootfs.ext4
	cp $(CURDIR)/output/br-har/images/rootfs.tar $(CURDIR)/output/har-rootfs.tar

br-har-prem: check_environment
	mkdir -p $(CURDIR)/output/br-har-prem
	$(MAKE) O=$(CURDIR)/output/br-har-prem BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot har_prem_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-har-prem/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-har-prem
	cp $(CURDIR)/output/br-har-prem/images/rootfs.ext4 $(CURDIR)/output/har-rootfs.ext4
	cp $(CURDIR)/output/br-har-prem/images/rootfs.tar $(CURDIR)/output/har-rootfs.tar

# simulation images
br-hrv-eqemu-base: check_environment
	mkdir -p $(CURDIR)/output/br-hrv-eqemu
	$(MAKE) O=$(CURDIR)/output/br-hrv-eqemu BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot hrv_eqemu_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-hrv-eqemu/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-hrv-eqemu
	cp $(CURDIR)/output/br-hrv-eqemu/images/bbl $(CURDIR)/output/hrv-eqemu-base-bbl
	cp $(CURDIR)/output/br-hrv-eqemu/images/rootfs.ext2 $(CURDIR)/output/hrv-eqemu-base-rootfs.ext2
br-hrv-eqemu: br-hrv-eqemu-base

# TOOLCHAINS
.PHONY: tc-hrv-obare tc-hrv-olinux tc-har-obare tc-har-olinux tc-pulp tc-llvm tc-llvm-debug

# host
tc-hrv-obare: check_environment
	mkdir -p $(CURDIR)/output/tc-hrv-obare/
	cd $(CURDIR)/output/tc-hrv-obare/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/hrv-obare.config ariane

tc-hrv-olinux: check_environment
	mkdir -p $(CURDIR)/output/tc-hrv-olinux/
	cd $(CURDIR)/output/tc-hrv-olinux/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/hrv-olinux.config hero br_real

tc-har-obare: check_environment
	mkdir -p $(CURDIR)/output/tc-har-obare/
	cd $(CURDIR)/output/tc-har-obare/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/har-obare.config

tc-har-olinux: check_environment
	mkdir -p $(CURDIR)/output/tc-har-olinux/
	cd $(CURDIR)/output/tc-har-olinux/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/har-olinux.config hero br_real

# accelerator
tc-pulp: check_environment
	mkdir -p $(CURDIR)/output/tc-pulp/
	cd $(CURDIR)/output/tc-pulp/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/pulp.config hero-unknown
	chmod -R u+w $(HERO_INSTALL) && ln -sf riscv32-unknown-elf $(HERO_INSTALL)/riscv32-hero-unknown-elf && chmod -R u-w $(HERO_INSTALL)

# llvm
tc-llvm: check_environment
	mkdir -p $(CURDIR)/output/tc-llvm/
	cd $(CURDIR)/output/tc-llvm/ && $(ROOT)/toolchain/setup-llvm.sh Release

tc-llvm-debug: check_environment
	mkdir -p $(CURDIR)/output/tc-llvm-debug/
	cd $(CURDIR)/output/tc-llvm-debug/ && $(ROOT)/toolchain/setup-llvm.sh Debug

# SDK
.PHONY: sdk-pulp-hrv sdk-pulp sdk-pulp-har sdk-hrv sdk-har

sdk-pulp-hrv: check_environment
	$(ROOT)/pulp/setup-sdk.sh hero-urania
sdk-pulp: sdk-pulp-hrv

sdk-pulp-har: check_environment
	$(ROOT)/pulp/setup-sdk.sh hero-arm64

sdk-hrv: check_environment br-hrv
	cd $(CURDIR)/output/br-hrv && $(ROOT)/toolchain/install-sdk.sh

sdk-har: check_environment br-har
	cd $(CURDIR)/output/br-har && $(ROOT)/toolchain/install-sdk.sh

sdk-har-prem: check_environment br-har-prem
	cd $(CURDIR)/output/br-har-prem && $(ROOT)/toolchain/install-sdk.sh

# Utilities
.PHONY: util-hrv-openocd

util-hrv-openocd: check_environment
	mkdir -p $(CURDIR)/output/util-riscv-openocd/
	(export CCACHE=none; \
		export PATH=$(HERO_INSTALL)/bin:${PATH}; \
		cd $(ROOT)/util/riscv-openocd/; \
		./bootstrap; \
		cd $(CURDIR)/output/util-riscv-openocd/; \
		$(ROOT)/util/riscv-openocd/configure --prefix=$(HERO_INSTALL); \
		$(MAKE); \
		chmod -R u+w $(HERO_INSTALL); \
		$(MAKE) install; \
		chmod -R u-w $(HERO_INSTALL); \
	)

.PHONY: check_environment
check_environment:
	@env/check_environment.sh
