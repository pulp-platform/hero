PYTHON3 ?= python3
AEGIS_FILE_PATH ?= .
AEGIS_ROOT ?= .
CI_PROJECT_DIR ?= .

all: aegis-lint-ci.yml
all: aegis-synth-ci.yml
all: aegis-sim-ci.yml
all: aegis-doc-ci.yml

%-lint-ci.yml: scripts/genci.py $(CI_PROJECT_DIR)/$(AEGIS_FILE_PATH)/%.json
	$(PYTHON3) $^ lint $(AEGIS_ROOT) $(AEGIS_FILE_PATH) > $@

%-synth-ci.yml: scripts/genci.py $(CI_PROJECT_DIR)/$(AEGIS_FILE_PATH)/%.json
	$(PYTHON3) $^ synth $(AEGIS_ROOT) $(AEGIS_FILE_PATH) > $@

%-sim-ci.yml: scripts/genci.py $(CI_PROJECT_DIR)/$(AEGIS_FILE_PATH)/%.json
	$(PYTHON3) $^ sim $(AEGIS_ROOT) $(AEGIS_FILE_PATH) > $@

%-doc-ci.yml: scripts/genci.py $(CI_PROJECT_DIR)/$(AEGIS_FILE_PATH)/%.json
	$(PYTHON3) $^ doc $(AEGIS_ROOT) $(AEGIS_FILE_PATH) > $@

clean:
	rm -f *-lint-ci.yml
	rm -f *-synth-ci.yml
	rm -f *-sim-ci.yml
	rm -f *-doc-ci.yml
