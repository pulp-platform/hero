BENDER := ../bender script vivado | sed 's/verilog_dir/include_dirs/'# TODO: update Bender to fix this and simset
BENDER_FILES := ../bender ../Bender.yml ../Bender.lock
DEFINE_TCLS := \
    vivado_ips/define_defines.tcl \
    vivado_ips/define_includes.tcl \
    vivado_ips/define_sources.tcl
VIVADO := vivado-2019.1.1 vivado -mode batch

.PHONY: all
all: hero_zcu102

hero_zcu102: vivado_ips/pulp_zcu102 ${DEFINE_TCLS}
	${VIVADO} -source hero_zcu102.tcl

vivado_ips/pulp_zcu102: ${DEFINE_TCLS}
	cd vivado_ips && ${VIVADO} -source pulp_zcu102.tcl

zcu102/src/pulp_zcu102.v: src/pulp.py src/pulp.template_v
	cd src && ./pulp.py > ../$@

vivado_ips/define_defines.tcl: $(BENDER_FILES)
	${BENDER} | sed -n '/^set_property verilog_define/,/^\] \[current_fileset\]/p' > $@

vivado_ips/define_includes.tcl: $(BENDER_FILES)
	${BENDER} | sed -n '/^set_property include_dirs/,/^\] \[current_fileset\]/p;/^\] \[current_fileset\]/q' > $@

vivado_ips/define_sources.tcl: $(BENDER_FILES)
	${BENDER} | sed -n '/^set_property include_dirs/q;p' > $@

../bender: ../Makefile
	make -C .. bender

.PHONY: clean
clean:
	rm -rf hero_zcu102
	rm -f vivado_ips/{component.xml,define_*.tcl}
	rm -rf vivado_ips/{pulp_zcu102,xgui}
	rm -f {,vivado_ips/}vivado*.{jou,log,str}
