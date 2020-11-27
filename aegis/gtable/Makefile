SHELL := /bin/bash
PYTHON ?= /home/tbenz/opt/python3.7/bin/python3
AEGIS_FILE_PATH ?= ..

gtable_% : scripts/upload.py $(AEGIS_FILE_PATH)/aegis.json
	$(PYTHON) $^ $* $(shell cd $(AEGIS_FILE_PATH); git rev-parse HEAD; git describe --tags --exact-match 2> /dev/null || git symbolic-ref -q --short HEAD || git rev-parse --short HEAD)
