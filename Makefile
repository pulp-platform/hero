
SHELL=bash


BLUE=\033[0;34m
BOLD_RED=\033[1;31m
NC=\033[0m # No Color
BOLD=\033[1m
STD=\033[0m

PKG_DIR ?= $(PWD)/install

export VSIM_PATH=$(PKG_DIR)
export PULP_PATH=$(PWD)

export MSIM_LIBS_PATH=$(VSIM_PATH)/modelsim_libs

export IPS_PATH=$(PULP_PATH)/ips
export RTL_PATH=$(PULP_PATH)/rtl
export TB_PATH=$(PULP_PATH)/rtl/tb

define declareInstallFile

$(VSIM_PATH)/$(1): sim/$(1)
	install -v -D sim/$(1) $$@

INSTALL_HEADERS += $(VSIM_PATH)/$(1)

endef

INSTALL_FILES += tcl_files/config/vsim_ips.tcl
INSTALL_FILES += modelsim.ini
INSTALL_FILES += $(shell cd sim && find boot -type f)
INSTALL_FILES += $(shell cd sim && find tcl_files -type f)
INSTALL_FILES += $(shell cd sim && find waves -type f)

RUN_THREADS = 5

export PULP_ARTIFACTORY_USER=pulp:SFaMjrsckj3DRjjT7rKt


GF22_BE_PATH=$(CURDIR)/gf22fdx
MK_BACKEND_GF22=$(GF22_BE_PATH)/Makefile

SDK_MODULES?=--g runtime --m dpi-models --m sdk_install


$(foreach file, $(INSTALL_FILES), $(eval $(call declareInstallFile,$(file))))

BRANCH ?= master


#########################################################################
### HELP 
#########################################################################
help:
	@echo -e "##############################################"
	@echo -e "## MARSELLUS available makefile targets are:"
	@echo -e "##############################################"

	@echo -e "## IPs targets"
	@echo -e " - ${BOLD_RED}clean_IPdatabase${STD}: remove the ips directory and the __pychache__"
	@echo -e " - ${BOLD_RED}update_ips${STD}: clone or update all MARSELLUS used IPS (ips_list.yml) in 'fe/ips' folder. Also call 'update_sim' target"
	@echo -e " - ${BOLD_RED}diff_ips${STD}: check (git status) modifications in all MARSELLUS used IPS"
	@echo -e " - ${BOLD_RED}gen_ips_sim_scripts${STD}: generate all sim scripts for IPS (ips_list.yml)"
	@echo -e " - ${BOLD_RED}gen_ips_syn_scripts${STD}: generate all synth scripts for IPS (ips_list.yml)"
	@echo -e ""
#	@echo -e "## Simulation environment targets"
#	@echo -e " - ${BOLD_RED}update_sim${STD}: clone or update all MARSELLUS RTL simulation environment in 'sim' folder: tb, vsim and xcsim"
#	@echo -e " - ${BOLD_RED}diff_sim${STD}: check (git status) modifications in sim repository"
#	@echo -e ""
	@echo -e "## RTL platform targets for Mentor Questasim"
	@echo -e " - ${BOLD_RED}update_rtl${STD}: update (git pull) RTL platform"
	@echo -e " - ${BOLD_RED}diff_rtl${STD}: check (git status) modifications in RTL platform"
	@echo -e " - ${BOLD_RED}clean_rtl${STD}: clean compiled RTL platform"
	@echo -e " - ${BOLD_RED}build_rtl${STD}: compile RTL platform"
#	@echo -e " - ${BOLD_RED}build_syn_netlist_ulpcluster${STD}: compile MARSELLUS platform with ulpcluster modelled as a syn netlist without SDF"
#	@echo -e " - ${BOLD_RED}build_layout_netlist_ulpcluster${STD}: compile MARSELLUS platform with ulpcluster modelled as a post pnr netlist without SDF"
#	@echo -e " - ${BOLD_RED}check_rtl_todolist${STD}: generate a report file of remaining TODO, FIXME items existing in RTL source files"
	@echo -e ""
#	@echo -e "## RTL platform targets for Cadence Xcelium"
#	@echo -e " - ${BOLD_RED}clean_rtl_xcelium${STD}: clean compiled RTL platform"
#	@echo -e " - ${BOLD_RED}build_rtl_xcelium${STD}: compile RTL platform"
#	@echo -e " - ${BOLD_RED}build_rtl_xcelium_lp${STD}: compile RTL platform with LP CPF"
#	@echo -e ""
	@echo -e "## SDK targets"
	@echo -e " - ${BOLD_RED}update_pulp_sdk${STD}: clone or update sdk folder with pulp-builder and pulp-sdk repositories"
	@echo -e " - ${BOLD_RED}update_pulp_sdk_noethz${STD}: clone or update sdk folder with pulp-builder and pulp-sdk repositories (run this if not on eth machines)"
# @echo -e " - ${BOLD_RED}diff_sdk${STD}: check modifications in sdk repositories"
#	@echo -e " - ${BOLD_RED}build_sdk${STD}: build SDK (plpbuild <MODULES> clean build) when modifications exists in 'pulp-builder' repository (runner, ...)"
# @echo -e " - ${BOLD_RED}import_bootcode${STD}: import compiled boot_code for ROM by 'build_sdk' target in 'sim/vsim/boot' folder and generate CDE format file"
	@echo -e ""
	@echo -e "## Testsuite targets"
	@echo -e " - ${BOLD_RED}update_tests${STD}: clone or update tests repositories (tests_list.sh) into 'tests' folder"
#	@echo -e " - ${BOLD_RED}hello_world${STD}: run hello_world app on MARSELLUS RTL"
#	@echo -e " - ${BOLD_RED}diff_tests${STD}: check (git status) modifications in all tests repositories"
	@echo -e ""
	@echo -e "## Setup environment"
	@echo -e " - ${BOLD_RED}setup_sdk${STD}: configure sdk for MARSELLUS"
	@echo -e " - ${BOLD_RED}setup_sdk_noethz${STD}: configure sdk for MARSELLUS (run this if not on eth machines)"
	@echo -e " - ${BOLD_RED}vsim_conf${STD}: configure vsim path for MARSELLUS RTL"
	@echo -e " - ${BOLD_RED}setup_env${STD}: setup sdk and vsim path for MARSELLUS"
	@echo -e " - ${BOLD_RED}setup_env_noethz${STD}: setup sdk and vsim path for MARSELLUS (run this if not on eth machines)"	
	@echo -e ""
	@echo -e "## Physical Implementation targets"
#	@echo -e " - ${BOLD_RED}update_be${STD}: clone or update backend views of MARSELLUS into 'be' folder"
#	@echo -e " - ${BOLD_RED}diff_be${STD}: ccheck (git status) modifications in backend views of MARSELLUS into 'be' folder"
	@echo -e " - ${BOLD_RED}update_gf22fdx${STD}: clone or update gf22fdx repository of MARSELLUS used for synth, physical implementation, pa, sta and signoff"
#	@echo -e " - ${BOLD_RED}diff_gf22fdx${STD}: check (git status) modifications in gf22fdx repository"
#	@echo -e " - ${BOLD_RED}synth_ulpcluster${STD}: run Genus multi-mode, single-corner (SS_0.72V_M40C) low power synthesis for ULPCLUSTER domain"
#	@echo -e " - ${BOLD_RED}synth_ulpcluster_dft${STD}: run Genus multi-mode, single-corner (SS_0.72V_M40C) low power synthesis for CULPLUSTER domain with DFT insertion"
#	@echo -e " - ${BOLD_RED}synth_ulpcluster_mmmc${STD}: run Genus multi-mode, multi-corner low power synthesis for ULPCLUSTER domain"
#	@echo -e " - ${BOLD_RED}synth_ulpcluster_mmmc_dft${STD}: run Genus multi-mode, multi-corner low power synthesis for ULPCLUSTER domain with DFT insertion"
#	@echo -e " - ${BOLD_RED}synth_pulp_chip${STD}: run Genus low power synthesis for PULP_CHIP domain"
#	@echo -e ""
#	@echo -e "## Publish targets"
#	@echo -e " - ${BOLD_RED}publish_synth_ulpcluster_nondft${STD}: copy usefull outputs, logs, reports fron ULPCLUSTER genus synthesis folder without DFT to 'be' folder when you want to publish a new release"
#	@echo -e " - ${BOLD_RED}publish_synth_ulpcluster_dft${STD}: copy usefull outputs, logs, reports fron ULPCLUSTER genus synthesis folder with DFT to 'be' folder when you want to publish a new release"
	@echo -e "##############################################"

#########################################################################
### RTL platform
#########################################################################
clean_IPdatabase:
	rm -rf ips
	rm -rf ips
	rm -rf ./scripts/__pychache__
update_ips:
	@./scripts/update-ips

gen_ips_sim_scripts:
	@./scripts/generate-scripts

gen_ips_syn_scripts:
	@./scripts/generate-scripts-syn

diff_ips:
	@echo -e "##############################################"
	@echo -e "Check diff for fe/ips"
	@echo -e "##############################################"
	@./scripts/diff-ips

diff_rtl:
	@echo -e "##############################################"
	@echo -e "Check diff for root project"
	@echo -e "##############################################"
	@git status

clean_rtl:
ifdef PKG_DRI
	@rm -rf $(PKG_DIR)
endif
	@cd sim  && make clean

update_rtl:
	@git pull

build_rtl: 
	@mkdir -p $(VSIM_PATH)
	@cd sim/  && make lib build opt

build_tb:
	@cd sim/  && make build_tb








vopt:
	export VOPT_FLOW=1 && cd $(VSIM_PATH) && vsim -64 -c -do "source tcl_files/config/vsim.tcl; quit"

import_bootcode:
	cd sim/boot && objcopy --srec-len 1 --output-target=srec ${PULP_SDK_HOME}/install/bin/boot-pulpissimo boot-pulpissimo.s19
	cd sim/boot && s19toboot.py boot-pulpissimo.s19 pulpissimo

#########################################################################
### PULP SDK
#########################################################################

update_pulp_sdk:

	@export SDK_GET_SOURCES=1 && ./scripts/update-sdk

update_pulp_sdk_noethz:
	./scripts/update-sdk-noethz

build_pulp_sdk:


#########################################################################
### PULP TESTS
#########################################################################


update_tests:
	@./scripts/update-tests.sh


#########################################################################
### Setup environment
#########################################################################

setup_sdk:
	source ./setup/sdk.sh

setup_sdk_noethz:
	source ./setup/sdk_precompiled.sh

vsim_conf:
	source ./setup/vsim.sh

setup_env:
	source ./setup/setup_eth.sh

setup_env_noethz:
	source ./setup/setup_env_noethz.sh

#########################################################################
### Physical Implementation targets
#########################################################################

update_gf22fdx:
	source ./scripts/update-gf22fdx.sh

#########################################################################
### CONTINUOUS INTEGRATION ---- MARSELLUS
#########################################################################


# GITLAB CI
# continuous integration on gitlab

checkout:
	git submodule update --init
	./scripts/update-ips-ci

# generic clean and build targets for the platform
clean:
	rm -rf $(VSIM_PATH)
	cd sim && $(MAKE) clean

build:
	cd sim && $(MAKE) lib build opt
	cp -r rtl/tb/* $(VSIM_PATH)

# sdk specific targets
install: $(INSTALL_HEADERS)

sdk-gitlab:
	sdk-releases/get-sdk-2019.11.03-CentOS_7.py; \

# the gitlab runner needs a special configuration to be able to access the
# dependent git repositories
test-checkout-gitlab:
	./scripts/update-tests-gitlab

# test with sdk release
test-gitlab:
	source env/env-sdk-2019.11.03.sh; \
	source pkg/sdk/2019.11.03/configs/pulp.sh; \
	source pkg/sdk/2019.11.03/configs/platform-rtl.sh; \
	cd tests && plptest --threads 16 --stdout

# test with built sdk
test-gitlab2:
	cd pulp-builder; \
	source sdk-setup.sh; \
	source configs/pulp.sh; \
	source configs/rtl.sh; \
	cd ../tests && plptest --threads 16 --stdout