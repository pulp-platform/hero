puts "${Green}Analyzing event_unit_flex ${NC}"

puts "${Green}--> compile event_unit_flex${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/event_unit_flex/./rtl/event_unit_core.sv
analyze -format sverilog  -work work ${IPS_PATH}/event_unit_flex/./rtl/event_unit_interface_mux.sv
analyze -format sverilog  -work work ${IPS_PATH}/event_unit_flex/./rtl/event_unit_top.sv
analyze -format sverilog  -work work ${IPS_PATH}/event_unit_flex/./rtl/soc_periph_fifo.sv
analyze -format sverilog  -work work ${IPS_PATH}/event_unit_flex/./rtl/interc_sw_evt_trig.sv
analyze -format sverilog  -work work ${IPS_PATH}/event_unit_flex/./rtl/hw_barrier_unit.sv
analyze -format sverilog  -work work ${IPS_PATH}/event_unit_flex/./rtl/hw_mutex_unit.sv
analyze -format sverilog  -work work ${IPS_PATH}/event_unit_flex/./rtl/hw_dispatch.sv
analyze -format sverilog  -work work ${IPS_PATH}/event_unit_flex/./rtl/periph_FIFO_id.sv
