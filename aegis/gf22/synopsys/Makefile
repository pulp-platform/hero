SHELL := /bin/bash

PYTHON3 ?= python3
RPT_DIR ?= reports
OUT_DIR ?= out
ALIB_DIR ?= alib/alib-52
MEM_DIR ?= ../mems
SYNDE ?= synopsys-2019.12-kgf de_shell -64bit
AEGIS_FILE_PATH ?= ../..

PDK_BASE ?= /usr/pack/gf-22-kgf/invecas/std/2020.01
ALIB_LOC ?= /synopsys.dz/alib-52

ALIBS = $(wildcard $(PDK_BASE)/*$(ALIB_LOC)/*.db.alib)

$(RPT_DIR) $(OUT_DIR) $(ALIB_DIR):
	mkdir -p $@

# collect alib cache
$(ALIB_DIR)/alibs.txt: | $(ALIB_DIR)
	$(foreach lib,$(ALIBS),ln -s $(lib) $(addprefix $(ALIB_DIR)/,$(notdir $(lib)));)
	echo $(ALIBS) > $@

# top synthesis script for aegis test
scripts/%.synth.tcl: scripts/gensynth.py $(AEGIS_FILE_PATH)/aegis.json
	$(PYTHON3) $^ $* > $@

# memory loading script for aegis test
scripts/%.mems.tcl: scripts/genmems.py ../mems/%.mems.txt
	$(PYTHON3) $^ $* > $@

# stub memory loading script for aegis test
scripts/%.mems.tcl:
	touch $@

# clean SYNDE temporary files
clean_synde:
	rm -f filenames_*.log
	rm -f default.html*
	rm -f default.svf
	rm -rf .DE_log_snapshot_*
	rm -rf WORK

# clean everything (excludes memory cache)
clean: clean_synde
	rm -rf $(RPT_DIR)
	rm -rf $(OUT_DIR)
	rm -rf $(ALIB_DIR)
	rm -f scripts/*.synth.tcl
	rm -f scripts/*.mems.tcl

# clean memory macro lists and wrappers
# TODO: should this be done on clean or not? Time-safety tradeoff?
clean_mems:
	$(MAKE) -C ../mems clean_test

.SECONDARY:

# run synthesis for aegis test
synth_%: scripts/%.synth.tcl | $(RPT_DIR) $(OUT_DIR) $(ALIB_DIR)/alibs.txt
	$(SYNDE) -no_log -x "source $<"
	$(MAKE) clean_synde
