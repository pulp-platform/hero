zcu102/src/pulp_zcu102.v: src/pulp.py src/pulp.template_v
	cd src && ./pulp.py > ../$@

BENDER_FILES := ../bender ../Bender.yml ../Bender.lock
BENDER := ../bender script vivado | sed 's/verilog_dir/include_dirs/'# TODO: update Bender to fix this and simset

vivado_ips/define_defines.tcl: $(BENDER_FILES)
	${BENDER} | sed -n '/^set_property verilog_define/,/^\] \[current_fileset\]/p' > $@

vivado_ips/define_includes.tcl: $(BENDER_FILES)
	${BENDER} | sed -n '/^set_property include_dirs/,/^\] \[current_fileset\]/p;/^\] \[current_fileset\]/q' > $@

vivado_ips/define_sources.tcl: $(BENDER_FILES)
	${BENDER} | sed -n '/^set_property include_dirs/q;p' > $@

../bender: ../Makefile
	make -C .. bender
