puts "${Green}Analyzing tech_cells_generic ${NC}"


puts "${Green}--> compile tech_cells_rtl_synth${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/tech_cells_generic/src/pulp_clock_gating_async.sv

