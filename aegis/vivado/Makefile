SHELL := /bin/bash

RPT_DIR ?= reports
VIVADO ?= vivado-2019.1.1 vivado
VIVADO_MODE ?= -mode batch
PYTHON3 ?= python3

AEGIS_FILE_PATH ?= ..


$(RPT_DIR):
	mkdir -p $@

# clean everything
clean:
	rm -rf $(RPT_DIR)
	rm -rf scripts/*.synth.tcl
	rm -rf .Xil
	rm *.jou

# top synthesis script for aegis test
scripts/%.synth.tcl: ../scripts/gensynth.py $(AEGIS_FILE_PATH)/aegis.json
	$(PYTHON3) $^ vivado/$* scripts/synth.tcl > $@

# run synthesis for aegis test
vivado_%: scripts/%.synth.tcl | $(RPT_DIR)
	$(VIVADO) $(VIVADO_MODE) -source $< -verbose -log $(RPT_DIR)/$*.vivado.log
