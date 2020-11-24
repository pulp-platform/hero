SHELL := /bin/bash
PYTHON ?= /home/tbenz/opt/python3.7/bin/python3
OUTDIR ?= out
EXT ?= png
DOT_BIN ?= dot
DOT_OPTIONS ?= -Granksep=1.25 -v -Ln20
AEGIS_FILE_PATH ?= ..

$(OUTDIR):
	mkdir -p $@

graph_% $(OUTDIR)/%.gv $(OUTDIR)/%.$(EXT) $(OUTDIR)/%.svg: scripts/gengraph.py $(AEGIS_FILE_PATH)/aegis.json | $(OUTDIR)
	$(PYTHON) $^ $* 1> $(OUTDIR)/$*.gv
	$(DOT_BIN) $(OUTDIR)/$*.gv -T$(EXT) -o $(OUTDIR)/$*.$(EXT) $(DOT_OPTIONS)
	$(DOT_BIN) $(OUTDIR)/$*.gv -Tsvg -o $(OUTDIR)/$*.svg $(DOT_OPTIONS)

clean:
	rm -rf $(OUTDIR)
