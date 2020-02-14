BENDER := ../bender script vivado | sed 's/verilog_dir/include_dirs/'# TODO: update Bender to fix this and simset
BENDER_FILES := ../bender ../Bender.yml ../Bender.lock
DEFINE_TCLS := \
    vivado_ips/define_defines.tcl \
    vivado_ips/define_includes.tcl \
    vivado_ips/define_sources.tcl

ifeq ($(VIVADO),)
VIVADO := vivado-2019.1.1 vivado
endif

VIVADO_OPT :=-mode batch

.PHONY: all
all: hero_exilzcu102

hero_exilzcu102: vivado_ips/pulp_txilzu9eg ${DEFINE_TCLS}
	${VIVADO} ${VIVADO_OPT} -source hero_exilzcu102.tcl

vivado_ips/pulp_txilzu9eg: ${DEFINE_TCLS}
	cd vivado_ips && ${VIVADO} ${VIVADO_OPT} -source pulp_txilzu9eg.tcl

vivado_ips/pulp_txilzu9eg.v: src/pulp.py src/pulp.template_v
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
	rm -rf hero_exilzcu102
	rm -f vivado_ips/{component.xml,define_*.tcl}
	rm -rf vivado_ips/{pulp_txilzu9eg,xgui}
	rm -f {,vivado_ips/}vivado*.{jou,log,str}
