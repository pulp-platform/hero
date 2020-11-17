# Copyright ETH Zurich 2019
VLOG_ARGS += -suppress vlog-2583 -suppress vlog-13314 -suppress vlog-13233
#VLOG_ARGS += -define PRINT_CORE_MEM_ACCESSES

.PHONY: vsim/compile.tcl
vsim/compile.tcl: bender
	echo 'set ROOT [file normalize [file dirname [info script]]/..]' > $@
	./bender script vsim \
		--vlog-arg="$(VLOG_ARGS)" \
		-t rtl -t test \
		| grep -v "set ROOT" >> $@

bender: Makefile
	curl --proto '=https' --tlsv1.2 -sSf https://fabianschuiki.github.io/bender/init | sh -s 0.21.0
	touch bender
