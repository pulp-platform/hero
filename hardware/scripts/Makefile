
# ---- Test-specific variables ----
# ---------------------------------

# The CI runner may change project root after script generation -> substitute it with a variable
ifdef CI_PROJECT_DIR
relativize := sed "s|$(realpath $(CI_PROJECT_DIR))|$$\{CI_PROJECT_DIR\}|"
else
relativize := cat
endif

scripts/analyze.tcl: ../Bender.yml
	cd ../; bender script synopsys -t rtl -t synthesis | $(relativize) > scripts/analyze.tcl

scripts/flist.txt: ../Bender.yml
	cd ../; bender script flist -t rtl -t synthesis | $(relativize) > scripts/flist.txt

scripts/analyze_vivado.tcl: ../Bender.yml
	cd ../; bender script vivado -t rtl -t synthesis | $(relativize) > scripts/analyze_vivado.tcl

scripts/compile_vsim.tcl: ../Bender.yml
	cd ../; bender script vsim -t test $(vsimflags_$*) | $(relativize) > scripts/compile_vsim.tcl

all: scripts/analyze.tcl
all: scripts/flist.txt
all: scripts/analyze_vivado.tcl
all: scripts/compile_vsim.tcl

clean:
	rm -f scripts/analyze.tcl
	rm -f scripts/flist.txt
	rm -f scripts/analyze_vivado.tcl
	rm -f scripts/compile_vsim.tcl
