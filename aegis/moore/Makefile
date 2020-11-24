SHELL := /bin/bash
MOORE ?= moore
PYTHON3 ?= python3

OUTDIR ?= out
RPTDIR ?= reports

AEGIS_FILE_PATH ?= ..

# Strip control characters from colored output
strip_ctl_chars = sed -e "s/\x1b\[.\{0,5\}m//g"

$(OUTDIR) $(RPTDIR):
	mkdir -p $@

# Invoke Moore, create return code for it
moore_% $(RPTDIR)/%_moore.rpt $(OUTDIR)/%.llhd: $(AEGIS_FILE_PATH)/aegis.json | $(OUTDIR) $(RPTDIR)
	mkfifo rpt_ascii_$*
	$(MOORE) $(shell $(PYTHON3) scripts/elab.py $^ $*) 1> $(OUTDIR)/$*.llhd 2> rpt_ascii_$* &
	cat <rpt_ascii_$* | $(strip_ctl_chars) > $(RPTDIR)/$*_moore.rpt
	rm rpt_ascii_$*
	tail -n 1000 $(RPTDIR)/$*_moore.rpt | ( ! grep -q "error: \|compiler bug: " )

clean:
	rm -rf $(OUTDIR)
	rm -rf $(RPTDIR)
	rm -f rpt_ascii_*
