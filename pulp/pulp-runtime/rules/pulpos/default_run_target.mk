ifeq '$(platform)' 'gvsoc'
run:
	pulp-run --platform=$(platform) --config=$(PULPRUN_TARGET) --dir=$(TARGET_BUILD_DIR) --binary=$(TARGETS) $(runner_args) prepare run
endif

ifeq '$(platform)' 'rtl'

$(TARGET_BUILD_DIR)/modelsim.ini:
	ln -s $(VSIM_PATH)/modelsim.ini $@

$(TARGET_BUILD_DIR)/boot:
	ln -s $(VSIM_PATH)/boot $@

$(TARGET_BUILD_DIR)/tcl_files:
	ln -s $(VSIM_PATH)/tcl_files $@

$(TARGET_BUILD_DIR)/waves:
	ln -s $(VSIM_PATH)/waves $@


run: $(TARGET_BUILD_DIR)/modelsim.ini  $(TARGET_BUILD_DIR)/boot $(TARGET_BUILD_DIR)/tcl_files $(TARGET_BUILD_DIR)/waves
	$(PULPRT_HOME)/bin/stim_utils.py --binary=$(TARGETS) --vectors=$(TARGET_BUILD_DIR)/vectors/stim.txt

ifdef gui
	cd $(TARGET_BUILD_DIR) && export VSIM_RUNNER_FLAGS="+ENTRY_POINT=0x1c008080 -gLOAD_L2=JTAG -dpicpppath /usr/bin/g++ -permit_unmatched_virtual_intf -gBAUDRATE=115200" && export VOPT_ACC_ENA="YES" && vsim -64 -do 'source $(VSIM_PATH)/tcl_files/config/run_and_exit.tcl' -do 'source $(VSIM_PATH)/tcl_files/run.tcl; '
else
	cd $(TARGET_BUILD_DIR) && export VSIM_RUNNER_FLAGS="+ENTRY_POINT=0x1c008080 -gLOAD_L2=JTAG -dpicpppath /usr/bin/g++ -permit_unmatched_virtual_intf -gBAUDRATE=115200" && vsim -64 -c -do 'source $(VSIM_PATH)/tcl_files/config/run_and_exit.tcl' -do 'source $(VSIM_PATH)/tcl_files/run.tcl; run_and_exit;'
endif

endif

ifeq '$(platform)' 'fpga'
run:
	$(PULPRT_HOME)/bin/elf_run_genesys2.sh $(TARGETS)
endif
