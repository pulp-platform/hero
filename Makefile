ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

.PHONY: all br-genesys2-ariane br-zynqmp-zcu102 br-hero-riscv64 br-hero br-hero-aarch64 br-qemu-ariane tc-ariane-bare tc-ariane-linux tc-pulp pulp-sdk hero-sdk hero-llvm tools tools-isa-sim tools-openocd

all: br-ariane br-hero

# buildroot
br-genesys2-ariane:
	mkdir -p $(CURDIR)/output/br-genesys2-ariane
	$(MAKE) O=$(CURDIR)/output/br-genesys2-ariane BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot genesys2_ariane_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-genesys2-ariane/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-genesys2-ariane
	cp $(CURDIR)/output/br-ariane/images/bbl.bin $(CURDIR)

br-zynqmp-zcu102:
	mkdir -p $(CURDIR)/output/br-zynqmp-zcu102
	$(MAKE) O=$(CURDIR)/output/br-zynqmp-zcu102 BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot zynqmp_zcu102_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-zynqmp-zcu102/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-zynqmp-zcu102

br-hero-riscv64:
	mkdir -p $(CURDIR)/output/br-hero-riscv64
	$(MAKE) O=$(CURDIR)/output/br-hero-riscv64 BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot hero_riscv64_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-hero-riscv64/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-hero-riscv64
br-hero: br-hero-riscv64

br-hero-aarch64:
	mkdir -p $(CURDIR)/output/br-hero-aarch64
	$(MAKE) O=$(CURDIR)/output/br-hero-aarch64 BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot hero_aarch64_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-hero-aarch64/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-hero-aarch64

br-qemu-ariane:
	mkdir -p $(CURDIR)/output/br-qemu-ariane
	$(MAKE) O=$(CURDIR)/output/br-qemu-ariane BR2_EXTERNAL=$(ROOT) -C $(ROOT)/buildroot qemu_ariane_defconfig
	if [ -a $(CURDIR)/local.cfg ]; then cat $(CURDIR)/local.cfg >> $(CURDIR)/output/br-qemu-ariane/.config; fi
	$(MAKE) -C $(CURDIR)/output/br-qemu-ariane

# toolchain
tc-ariane-bare:
	mkdir -p $(CURDIR)/output/tc-ariane-bare/
	cd $(CURDIR)/output/tc-ariane-bare/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/ariane-bare.config ariane

tc-ariane-linux:
	mkdir -p $(CURDIR)/output/tc-ariane-linux/
	cd $(CURDIR)/output/tc-ariane-linux/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/ariane-linux.config hero br_real

tc-aarch64-bare:
	mkdir -p $(CURDIR)/output/tc-aarch64-bare/
	cd $(CURDIR)/output/tc-aarch64-bare/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/aarch64-bare.config

tc-aarch64-linux:
	mkdir -p $(CURDIR)/output/tc-aarch64-linux/
	cd $(CURDIR)/output/tc-aarch64-linux/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/aarch64-linux.config hero br_real

tc-pulp:
	mkdir -p $(CURDIR)/output/tc-pulp/
	cd $(CURDIR)/output/tc-pulp/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/pulp.config hero-unknown
	chmod -R u+w $(RISCV) && ln -sf $(RISCV)/riscv32-unknown-elf $(RISCV)/riscv32-hero-unknown-elf && chmod -R u-w $(RISCV)

# sdk
pulp-sdk:
	$(ROOT)/pulp/setup-sdk.sh hero-urania

hero-sdk: br-hero
	cd $(CURDIR)/output/br-hero-riscv64 && $(ROOT)/toolchain/install-sdk.sh

# llvm
hero-llvm:
	mkdir -p $(CURDIR)/output/hero-llvm/
	cd $(CURDIR)/output/hero-llvm/ && $(ROOT)/toolchain/setup-hero-llvm.sh Release

hero-llvm-debug:
	mkdir -p $(CURDIR)/output/hero-llvm-debug/
	cd $(CURDIR)/output/hero-llvm-debug/ && $(ROOT)/toolchain/setup-hero-llvm.sh Debug

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
