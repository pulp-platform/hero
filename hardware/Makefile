# Copyright ETH Zurich 2019
VLOG_ARGS += -suppress vlog-2583 -suppress vlog-13314 -suppress vlog-13233 ${DEFINES}
#VLOG_ARGS += -define PRINT_CORE_MEM_ACCESSES
VCS ?= vcs-2017.03
VCS_ARGS += -nc
VLOGAN_ARGS += $(VCS_ARGS) -timescale=1ps/1ps -assert svaext ${DEFINES}

.PHONY: vsim/compile.tcl
vsim/compile.tcl: bender test/remote_bitbang/librbs.so
	echo 'set ROOT [file normalize [file dirname [info script]]/..]' > $@
	./bender script vsim \
		--vlog-arg="$(VLOG_ARGS)" \
		-t rtl -t test \
		| grep -v "set ROOT" >> $@

.PHONY: vcs/compile.sh
vcs/compile.sh: bender test/remote_bitbang/librbs.so
	./bender script vcs \
		--vlogan-bin="$(VCS) vlogan" \
		--vhdlan-bin="$(VCS) vhdlan" \
		--vlog-arg="$(VLOGAN_ARGS)" \
		-t rtl -t test \
		| grep -v "set ROOT" > $@
	ex -s -c '3i|readonly THIS_DIR="$$(dirname "$$(readlink -f "$${BASH_SOURCE[0]}")")"' -c x $@
	ex -s -c '4i|readonly ROOT="$$(readlink -f "$${THIS_DIR}/..")"' -c x $@
	ex -s -c '5i|set -e' -c x $@ # abort on first compile error
	perl -i -00ne 'print unless /(?<!ROOT\/)test\//' $@ # exclude unsupported test code
	echo "$(VCS) vcs $(VCS_ARGS) -full64 pulp_tb -debug_access+all -notice" >> $@
	chmod +x $@

bender: Makefile
	curl --proto '=https' --tlsv1.2 -sSf https://iis-people.ee.ethz.ch/~andkurt/bender-init \
		| bash -s -- 0.16.0
	touch bender

test/remote_bitbang/librbs.so: test/remote_bitbang/*.c test/remote_bitbang/*.h
	$(MAKE) -C test/remote_bitbang all
