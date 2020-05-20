puts "${Green}Analyzing fpu_div_sqrt_mvp ${NC}"

puts "${Green}--> compile div_sqrt_top_mvp${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/fpu_div_sqrt_mvp/hdl/defs_div_sqrt_mvp.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/fpu_div_sqrt_mvp/hdl/control_mvp.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/fpu_div_sqrt_mvp/hdl/div_sqrt_mvp_wrapper.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/fpu_div_sqrt_mvp/hdl/div_sqrt_top_mvp.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/fpu_div_sqrt_mvp/hdl/iteration_div_sqrt_mvp.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/fpu_div_sqrt_mvp/hdl/norm_div_sqrt_mvp.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/fpu_div_sqrt_mvp/hdl/nrbd_nrsc_mvp.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/fpu_div_sqrt_mvp/hdl/preprocess_mvp.sv
