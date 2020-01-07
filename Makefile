ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

# TOOLCHAINS
.PHONY: tc-pulp

# accelerator
tc-pulp:
	mkdir -p $(CURDIR)/output/tc-pulp/
	cd $(CURDIR)/output/tc-pulp/ && $(ROOT)/toolchain/build.sh $(ROOT)/toolchain/pulp.config hero-unknown
	chmod -R u+w $(HERO_INSTALL) && ln -sf $(HERO_INSTALL)/riscv32-unknown-elf $(HERO_INSTALL)/riscv32-hero-unknown-elf && chmod -R u-w $(HERO_INSTALL)

# SDK
.PHONY: sdk-pulp

sdk-pulp:
	$(ROOT)/pulp/setup-sdk.sh hero-huawei
