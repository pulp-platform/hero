SHELL := /bin/bash
MORTY ?= /home/tbenz/.cargo/bin/morty
PYTHON3 ?= python3

DOCDIR ?= doc
REPDIR ?= reports

AEGIS_FILE_PATH ?= ..


$(DOCDIR) $(REPDIR):
	mkdir -p $@

morty_% $(RPTDIR)/%_morty.rpt $(DOCDIR)/%/index.html: $(AEGIS_FILE_PATH)/aegis.json | $(DOCDIR) $(REPDIR)
	mkdir -p $(DOCDIR)/$*
	$(MORTY) $(shell $(PYTHON3) scripts/elab.py $^ $*) --doc $(DOCDIR)/$* > $(REPDIR)/$*.rpt

clean:
	rm -rf $(DOCDIR)
	rm -rf $(REPDIR)
