# Copyright ETH Zurich 2019
VLOG_ARGS += -suppress vlog-2583 -suppress vlog-13314 -suppress vlog-13233
#VLOG_ARGS += -define PRINT_CORE_MEM_ACCESSES
MORTY ?= morty
PYTHON ?= python3
PREFIX ?= hero_v2_
TMPDIR ?= /
MORTY_SYNTH_OPTIONS ?= -D SYNTHESIS -D VERILATOR -D TARGET_SYNTHESIS --strip-comments
MORTY_SIM_OPTIONS ?=
COMMIT ?= $(shell git rev-parse HEAD)
OUT_DIR ?= pickles
TMP_DIR ?= /dev/shm/hero_pickle

.PHONY: all
.PHONY: sim_pickle synth_pickle pickle

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

$(OUT_DIR)/$(PREFIX)synth_pickle_$(COMMIT).sv: hero_synth_sources.json scripts/reorg_pickle.py | $(OUT_DIR) $(TMP_DIR)
	$(MORTY) -f $< -p $(PREFIX) $(MORTY_SYNTH_OPTIONS) > $(TMP_DIR)/$(PREFIX)synth_pickle_$(COMMIT).sv
	$(PYTHON) scripts/reorg_pickle.py $(TMP_DIR)/$(PREFIX)synth_pickle_$(COMMIT).sv $@
	sed -i 's/$(PREFIX)tc_sram/tc_sram/g' $@
	rm -rf $(TMP_DIR)/

$(OUT_DIR)/$(PREFIX)sim_pickle_$(COMMIT).sv: hero_sim_sources.json | $(OUT_DIR)
	$(MORTY) -f $^ -p $(PREFIX) $(MORTY_SIM_OPTIONS) > $@

sim_pickle: $(OUT_DIR)/$(PREFIX)sim_pickle_$(COMMIT).sv

synth_pickle: $(OUT_DIR)/$(PREFIX)synth_pickle_$(COMMIT).sv

clean:
	rm -f vsim/compile.tcl
	rm -f hero_*_sources.json
	rm -rf $(OUT_DIR)/
