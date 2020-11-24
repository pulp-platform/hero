SHELL := /bin/bash

VERILATOR ?= verilator
PYTHON3 ?= python3

AEGIS_FILE_PATH ?= ..

# Set to parent directory iff not set
CI_PROJECT_DIR ?= ..

# TODO: can we make sure this fatals on errors? (.SHELLSTATUS needs GNU Make >= 4.2)
aegis_key = $(shell $(PYTHON3) -c "import json; print(json.load(open('$(1)'))['verilator']['$(2)']['$(3)'])")
subst_ci_dir = $(subst $${CI_PROJECT_DIR},$(CI_PROJECT_DIR),$(1))

# Translate
verilate_% %.verilate.log obj_%/V%: $(AEGIS_FILE_PATH)/aegis.json
	$(VERILATOR) --Mdir obj_$* \
		--cc $(addprefix $(call aegis_key,$<,$*,croot)/,$(call aegis_key,$<,$*,csources)) \
		$(call subst_ci_dir,$(shell cat $(call aegis_key,$<,$*,flist))) \
		--top-module $(call aegis_key,$<,$*,topmodule) --trace --exe
	$(MAKE) -C obj_$* -f V$*.mk | tee $*.verilate.log

# TODO: does this need further exit code annotation? Is there a convention?
verilator_% %.run.log: verilate_%
	obj_$*/V$* | tee  $*.run.log

clean:
	rm -rf obj_*
	rm -rf *.vcd
	rm -rf *.log
