HW_DIR = ../..
BENDER = $(HW_DIR)/bender

.PHONY: tcl/define_src_files.tcl
tcl/define_src_files.tcl: $(BENDER) tcl
	$(BENDER) script vivado -t synthesis -t zcu102 > $@

tcl:
	mkdir $@

$(BENDER): $(HW_DIR)/Makefile
	make -C $(HW_DIR) bender
