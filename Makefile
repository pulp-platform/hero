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
	$(ROOT)/pulp/setup-sdk.sh --no-checkout hero-huawei

# Bender
.PHONY: bender

bender:
	make -C "$(ROOT)/hardware" bender
	if [ -z $(HERO_INSTALL) ]; then echo "HERO_INSTALL not set!"; exit 1; fi
	chmod -R u+w "$(HERO_INSTALL)/bin"
	ln -sf "$(shell realpath --relative-to="$(HERO_INSTALL)/bin/" "$(ROOT)/hardware/bender")" "$(HERO_INSTALL)/bin/"
	chmod -R u-w "$(HERO_INSTALL)/bin"

# Virtual Platform
.PHONY: virtual-platform

virtual-platform:
	cd "$(ROOT)/pulp/virtual-platform" && \
	./scripts/build-gvsoc
