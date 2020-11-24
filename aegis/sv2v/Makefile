SHELL := /bin/bash
SV2V ?= /home/tbenz/opt/sv2v/bin/sv2v
PYTHON3 ?= python3

OUTDIR ?= out
RPTDIR ?= reports
TMPDIR ?= /dev/shm/aegis/sv2v

AEGIS_FILE_PATH ?= ..


$(OUTDIR) $(RPTDIR) $(TMPDIR):
	mkdir -p $@

sv2v_% $(RPTDIR)/%_sv2v.rpt out/%.v: $(AEGIS_FILE_PATH)/aegis.json | $(RPTDIR) $(TMPDIR) $(OUTDIR)
	$(PYTHON3) scripts/preprocess.py $^ $* $(TMPDIR)/$*/
	$(SV2V) $(shell $(PYTHON3) scripts/elab.py $^ $* $(TMPDIR)/$*/) 1> out/$*.v 2> $(RPTDIR)/$*_sv2v.rpt

clean:
	rm -rf $(OUTDIR)
	rm -rf $(RPTDIR)
	rm -rf $(TMPDIR)
