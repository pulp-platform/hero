SHELL := /bin/bash
SPYGLASS ?= spyglass-2019.06-kgf sg_shell
PYTHON3 ?= python3

RPTDIR ?= reports
PROJDIR ?= /dev/shm/aegis/spyglass

AEGIS_FILE_PATH ?= ..

$(RPTDIR) $(PROJDIR):
	mkdir -p $@

scripts/%_run.tcl: scripts/genscript.py $(AEGIS_FILE_PATH)/aegis.json | $(RPTDIR) $(PROJDIR)
	$(PYTHON3) $^ $* $(RPTDIR) $(PROJDIR) > scripts/$*_run.tcl

# create error return code when ERRORs or FATALs (unrelated to licenses) found
spyglass_%: scripts/%_run.tcl
	$(SPYGLASS) -tcl $^
	! grep "ERROR\|FATAL" reports/$*.*.summary.rpt | grep -v "###############"  | grep -v "license"

clean:
	rm -rf $(RPTDIR)
	rm -rf $(PROJDIR)
	rm -f  scripts/*_run.tcl
	rm -f *.log
	rm -f *.prj
