ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

.PHONY: all br-ariane br-hero br-qemu tc-ariane-bare tc-ariane-linux tc-pulp pulp-sdk hero-sdk hero-llvm tools tools-isa-sim tools-openocd

all: br-ariane br-hero

# buildroot
br-ariane:
	mkdir -p $(CURDIR)/output/br-ariane
	$(MAKE) O=$(CURDIR)/output/br-ariane BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot ariane_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-ariane/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-ariane
	cp $(CURDIR)/output/br-ariane/images/bbl.bin $(CURDIR)

br-hero:
	mkdir -p $(CURDIR)/output/br-hero
	$(MAKE) O=$(CURDIR)/output/br-hero BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot hero_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-hero/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-hero

br-qemu:
	mkdir -p $(CURDIR)/output/br-qemu
	$(MAKE) O=$(CURDIR)/output/br-qemu BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot qemu_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-qemu/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-qemu

# toolchain
tc-ariane-bare:
	mkdir -p $(CURDIR)/output/tc-ariane-bare/
	cd $(CURDIR)/output/tc-ariane-bare/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/ariane-bare.config ariane

tc-ariane-linux:
	mkdir -p $(CURDIR)/output/tc-ariane-linux/
	# NOTE: we add br_real suffix here as buildroot will use that suffix later
	cd $(CURDIR)/output/tc-ariane-linux/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/ariane-linux.config hero br_real

tc-pulp:
	mkdir -p $(CURDIR)/output/tc-pulp/
	cd $(CURDIR)/output/tc-pulp/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/pulp.config hero-unknown
	chmod -R u+w $(RISCV) && ln -sf $(RISCV)/riscv32-unknown-elf $(RISCV)/riscv32-hero-unknown-elf && chmod -R u-w $(RISCV)

# sdk
pulp-sdk:
	$(ROOT)/pulp/setup-sdk.sh hero-urania

hero-sdk: br-hero
	cd $(CURDIR)/output/br-hero && $(ROOT)/toolchain/install-sdk.sh

# llvm
hero-llvm:
	mkdir -p $(CURDIR)/output/hero-llvm/
	cd $(CURDIR)/output/hero-llvm/ && $(ROOT)/toolchain/setup-hero-llvm.sh

# tools
tools: tools-openocd

tools-openocd:
	mkdir -p $(CURDIR)/output/tools-openocd/
	(export CCACHE=none; \
		export PATH=$(RISCV)/bin:${PATH}; \
		cd $(ROOT)/tools/riscv-openocd/; \
		./bootstrap; \
		cd $(CURDIR)/output/tools-openocd/; \
		$(ROOT)/tools/riscv-openocd/configure --prefix=$(RISCV); \
		$(MAKE); \
		chmod -R u+w $(RISCV); \
		$(MAKE) install; \
		chmod -R u-w $(RISCV); \
	)
