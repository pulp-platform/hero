SHELL := /bin/bash
VERIBLE_LINT ?= /home/tbenz/opt/verible/verible-verilog-lint --parse_fatal
PYTHON ?= python3

AEGIS_FILE_PATH ?= ..

verible_% reports/%_verible.rpt: $(AEGIS_FILE_PATH)/aegis.json
	mkdir -p reports
	$(VERIBLE_LINT) $(shell $(PYTHON) scripts/elab.py $^ $*) > reports/$*_verible_lint.rpt

clean:
	rm -rf reports
