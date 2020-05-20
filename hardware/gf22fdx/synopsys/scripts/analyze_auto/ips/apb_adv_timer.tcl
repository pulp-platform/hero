puts "${Green}Analyzing apb_adv_timer ${NC}"

puts "${Green}--> compile apb_adv_timer${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/apb/apb_adv_timer/./rtl/adv_timer_apb_if.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/apb/apb_adv_timer/./rtl/comparator.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/apb/apb_adv_timer/./rtl/lut_4x4.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/apb/apb_adv_timer/./rtl/out_filter.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/apb/apb_adv_timer/./rtl/up_down_counter.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/apb/apb_adv_timer/./rtl/input_stage.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/apb/apb_adv_timer/./rtl/prescaler.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/apb/apb_adv_timer/./rtl/apb_adv_timer.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/apb/apb_adv_timer/./rtl/timer_cntrl.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/apb/apb_adv_timer/./rtl/timer_module.sv
