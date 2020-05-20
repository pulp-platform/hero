puts "${Green}Analyzing timer_unit ${NC}"

puts "${Green}--> compile timer_unit${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/timer_unit/./rtl/apb_timer_unit.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/timer_unit/./rtl/timer_unit.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/timer_unit/./rtl/timer_unit_counter.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/timer_unit/./rtl/timer_unit_counter_presc.sv
