# Copyright ETH Zurich 2019
VLOG_ARGS += -suppress vlog-2583 -suppress vlog-13314 -suppress vlog-13233
#VLOG_ARGS += -define PRINT_CORE_MEM_ACCESSES

SHELL = bash
PYTHON ?= python3

# morty config
MORTY ?= morty
PREFIX ?= hero_v2_
MORTY_SYNTH_OPTIONS ?= -D SYNTHESIS -D VERILATOR -D TARGET_SYNTHESIS --strip-comments
MORTY_SIM_OPTIONS ?=
OUT_DIR ?= pickles
TMP_DIR ?= /dev/shm/hero_pickle
DIRTY_ERROR ?= Your branch is dirty, please commit or remove all changes to ensure reproducibility

# Activate at your OWN risk!
OVERRIDE_DIRY_CHECK ?=

# metadata
COMMIT    ?= $(shell git rev-parse HEAD)
BRANCH    ?= $(shell git rev-parse --abbrev-ref HEAD)
DATE      ?= $(shell date '+%d/%m/%Y %H:%M:%S')
MORTY_VER ?= $(shell $(MORTY) -V)
HOST      ?= $(shell hostname)
REPO      ?= $(shell git config --get remote.origin.url)
DIRTY     ?= $(shell git diff --quiet || echo '(dirty)')

define meta
	echo '// Created automatically $(DIRTY)' >  $1
	echo '// morty_version: $(MORTY_VER)'    >> $1
	echo '// user:          $(USER)'         >> $1
	echo '// time:          $(HOST)'         >> $1
	echo '// date:          $(DATE)'         >> $1
	echo '// repository:    $(REPO)'         >> $1
	echo '// branch:        $(BRANCH)'       >> $1
	echo '// commit:        $(COMMIT)'       >> $1
	echo '// type:          $2'              >> $1
	echo                                     >> $1
endef

.PHONY: all
.PHONY: sim_pickle synth_pickle pickle
.PHONY: error_if_dirty

all: vsim/compile.tcl

pickle: sim_pickle synth_pickle

$(OUT_DIR) $(TMP_DIR):
	mkdir -p $@

vsim/compile.tcl: bender
	echo 'set ROOT [file normalize [file dirname [info script]]/..]' > $@
	./bender script vsim \
		--vlog-arg="$(VLOG_ARGS)" \
		-t rtl -t test \
		| grep -v "set ROOT" >> $@

bender: Makefile
	curl --proto '=https' --tlsv1.2 -sSf https://fabianschuiki.github.io/bender/init | sh -s 0.21.0
	touch bender

hero_synth_sources.json: bender
	./bender sources -f -t synthesis -t rtl -t default > $@

hero_sim_sources.json: bender
	./bender sources -f -t simulation -t rtl -t test -t default > $@

$(OUT_DIR)/$(PREFIX)synth_pickle.sv: hero_synth_sources.json scripts/reorg_pickle.py error_if_dirty | $(OUT_DIR) $(TMP_DIR)
	$(MORTY) -f $< -p $(PREFIX) $(MORTY_SYNTH_OPTIONS) > $(TMP_DIR)/$(PREFIX)synth_pickle.sv
	$(PYTHON) scripts/reorg_pickle.py $(TMP_DIR)/$(PREFIX)synth_pickle.sv $(TMP_DIR)/$(PREFIX)synth_pickle_reorder.sv
	$(call meta,$@,synth)
	cat $(TMP_DIR)/$(PREFIX)synth_pickle_reorder.sv >> $@
	sed -i 's/$(PREFIX)tc_sram/tc_sram/g' $@
	rm -rf $(TMP_DIR)/

$(OUT_DIR)/$(PREFIX)sim_pickle.sv: hero_sim_sources.json error_if_dirty | $(OUT_DIR)
	$(call meta,$@,sim)
	$(MORTY) -f $< -p $(PREFIX) $(MORTY_SIM_OPTIONS) >> $@

sim_pickle: $(OUT_DIR)/$(PREFIX)sim_pickle.sv

synth_pickle: $(OUT_DIR)/$(PREFIX)synth_pickle.sv

error_if_dirty:
	$(if $(OVERRIDE_DIRY_CHECK),,$(if $(shell git status | grep "nothing to commit, working tree clean"),,$(error $(DIRTY_ERROR))))

clean:
	rm -f vsim/compile.tcl
	rm -f hero_*_sources.json
	rm -rf $(OUT_DIR)/
