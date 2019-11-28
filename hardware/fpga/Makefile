zcu102/src/pulp_zcu102.v: src/pulp.py src/pulp.template_v
	cd src && ./pulp.py > ../$@

BENDER_FILES := ../bender ../Bender.yml ../Bender.lock

vivado_ips/define_srcs.tcl: $(BENDER_FILES)
	../bender script vivado | sed 's/verilog_dir/include_dirs/' > $@ # TODO: update Bender to fix this and simset

../bender: ../Makefile
	make -C .. bender
