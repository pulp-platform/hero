SHELL := /bin/bash
PERCENT := %

PYTHON3 ?= python3
SYNLC ?= synopsys lc_shell

FREEPDK45 ?= /usr/scratch/sulperg/tbenz/FreePDK45/FreePDK45
OPENRAM_HOME ?= /usr/scratch/sulperg/tbenz/OpenRAM/compiler
OPENRAM_TECH ?= /usr/scratch/sulperg/tbenz/OpenRAM/technology
MEM_OUTDIR ?= out
# DO NOT TOUCH: only TT works in FreePDK45
MEM_CORNER = TT_1p0V_25C
export

$(MEM_OUTDIR):
	mkdir -p $@

views = $(addprefix $(MEM_OUTDIR)/$(1),.gds .html .lef .log .lvs .py .sp .v _$(MEM_CORNER).lib)
db = $(MEM_OUTDIR)/$(1)_$(MEM_CORNER).db
catexists = $(shell cat $(wildcard $(1).mems.txt) /dev/null)

# run generator to generate views for one macro
$(call views,$(PERCENT)): scripts/genmem.py | $(MEM_OUTDIR)
	echo $* | $(PYTHON3) $(OPENRAM_HOME)/openram.py scripts/genmem

# generate DBs using library compiler
$(MEM_OUTDIR)/%.db: $(MEM_OUTDIR)/%.lib | $(MEM_OUTDIR)
	$(SYNLC) -no_init -no_log -batch -x "read_lib $<; write_lib $*_lib -output $@"

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
