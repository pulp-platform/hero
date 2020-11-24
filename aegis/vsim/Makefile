SHELL := /bin/bash

VSIM ?= vsim
PYTHON3 ?= python3

AEGIS_FILE_PATH ?= ..

# Create simulation directory per test
%.simdir:
	mkdir -p $@

# clean everything
clean:
	rm -f scripts/*.sim.tcl
	rm -rf *.simdir

# TODO: maintain, inc. compile into one library per compile script

# generate wrapper script: compile + lanch + run
scripts/%.sim.tcl: scripts/gensim.py $(AEGIS_FILE_PATH)/aegis.json
	${PYTHON3} $^ $* > $@

# run simulation for aegis test; returns error on nonzero error counts
vsim_%: scripts/%.sim.tcl | %.simdir
	cd $|; $(VSIM) -c -do "source ../$<"
