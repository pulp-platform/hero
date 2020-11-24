SHELL := /bin/bash
PERCENT := %

PYTHON3 ?= python3
SYNLC ?= synopsys-2019.12-kgf lc_shell

MEM_COMPILER ?= /usr/pack/gf-22-kgf/invecas/mem/2020.03/IN22FDX_MEMR1PH_COMPILER_FDK_RELV04R20SZ/bin/IN22FDX_MEM_genviews
MEM_OPTIONS ?= -generate lib
MEM_OUTDIR ?= out
MEM_CORNER ?= SSG_0P720V_0P000V_0P000V_M40C
export

$(MEM_OUTDIR):
	mkdir -p $@

views = $(MEM_OUTDIR)/cdl/$(1).cdl $(MEM_OUTDIR)/gds/$(1).gds $(MEM_OUTDIR)/lef/$(1).lef $(MEM_OUTDIR)/model/timing/lib/$(1)_104cpp_$(MEM_CORNER).lib
db = $(MEM_OUTDIR)/model/timing/lib/$(1)_104cpp_$(MEM_CORNER).db
catexists = $(shell cat $(wildcard $(1).mems.txt) /dev/null)

# run generator to generate views for one macro
$(call views,$(PERCENT)): | $(MEM_OUTDIR)
	$(MEM_COMPILER) $(MEM_OPTIONS) -out $(MEM_OUTDIR) -corner $(MEM_CORNER) -macro $*

# generate DBs using library compiler
$(MEM_OUTDIR)/model/timing/lib/%_104cpp_$(MEM_CORNER).db: $(MEM_OUTDIR)/model/timing/lib/%_104cpp_$(MEM_CORNER).lib | $(MEM_OUTDIR)
	$(SYNLC) -no_init -no_log -batch -x "read_lib $<; write_lib $*_104cpp_$(MEM_CORNER) -output $@"

# tc_sram wrapper with memories
src/%.tc_sram.sv: scripts/genwrap.py src/tc_sram.sv.template %.mems.txt
	$(PYTHON3) $^ > $@

# tc_sram wrapper with blackbox
src/%.tc_sram.sv: scripts/genwrap.py src/tc_sram.sv.template
	$(PYTHON3) $^ > $@

# clean only aegis test-related data, but not memory cache
clean_test:
	rm -f src/*.tc_sram.sv
	rm -f *.mems.txt

# clean everything including cache
clean: clean_test
	rm -rf $(MEM_OUTDIR)

.SECONDEXPANSION:
.SECONDARY:

# Generate views, db, and wrapper for a given aegis test
all_%: src/%.tc_sram.sv $$(foreach mem, $$(call catexists,$$*), $$(call views,$$(mem)) $$(call db,$$(mem)))
	@echo "Updated memories for '$*'"

#
