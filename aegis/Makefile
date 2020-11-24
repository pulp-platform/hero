PYTHON3 ?= python3
AEGIS_FILE_PATH ?= .

all: aegis-lint-ci.yml
all: aegis-synth-ci.yml
all: aegis-sim-ci.yml
all: aegis-doc-ci.yml

%-lint-ci.yml: scripts/genci.py $(AEGIS_FILE_PATH)/%.json
	$(PYTHON3) $^ lint > $@

%-synth-ci.yml: scripts/genci.py $(AEGIS_FILE_PATH)/%.json
	$(PYTHON3) $^ synth > $@

%-sim-ci.yml: scripts/genci.py $(AEGIS_FILE_PATH)/%.json
	$(PYTHON3) $^ sim > $@

%-doc-ci.yml: scripts/genci.py $(AEGIS_FILE_PATH)/%.json
	$(PYTHON3) $^ doc > $@

clean:
	rm -f *-lint-ci.yml
	rm -f *-synth-ci.yml
	rm -f *-sim-ci.yml
	rm -f *-doc-ci.yml
