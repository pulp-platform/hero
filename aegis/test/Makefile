examples = axi_dma foobar snitch a2o simple simple_twoclk ariane axi common_cells
analyzes = $(addsuffix /analyze.tcl, $(examples))
compiles_vsim = $(addsuffix /compile_vsim.tcl, $(examples))
analyzes_vivado = $(addsuffix /analyze_vivado.tcl, $(examples))
flists = $(addsuffix /flist.txt, $(examples))

# ---- Test-specific variables ----
vsimflags_axi = --vlog-arg="-svinputport=compat" --vlog-arg="-override_timescale 1ns/1ps" --vlog-arg="-suppress 2583"
# ---------------------------------

# The CI runner may change project root after script generation -> substitute it with a variable
ifdef CI_PROJECT_DIR
relativize := sed "s|$(realpath $(CI_PROJECT_DIR))|$$\{CI_PROJECT_DIR\}|"
else
relativize := cat
endif

%/analyze.tcl: %/Bender.yml
	cd $*; bender script synopsys | $(relativize) > analyze.tcl

%/flist.txt: %/Bender.yml
	cd $*; bender script flist | $(relativize) > flist.txt

%/analyze_vivado.tcl: %/Bender.yml
	cd $*; bender script vivado | $(relativize) > analyze_vivado.tcl

%/compile_vsim.tcl: %/Bender.yml
	cd $*; bender script vsim -t test $(vsimflags_$*) | $(relativize) > compile_vsim.tcl

all: $(analyzes)
all: $(analyzes_vivado)
all: $(flists)
all: $(compiles_vsim)

clean:
	rm -f $(analyzes)
	rm -f $(analyzes_vivado)
	rm -f $(flists)
	rm -f $(compiles_vsim)
