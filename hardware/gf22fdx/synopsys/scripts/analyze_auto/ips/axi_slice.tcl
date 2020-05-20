puts "${Green}Analyzing axi_slice ${NC}"

puts "${Green}--> compile axi_slice${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_slice/src/axi_single_slice.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_slice/src/axi_ar_buffer.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_slice/src/axi_aw_buffer.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_slice/src/axi_b_buffer.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_slice/src/axi_r_buffer.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_slice/src/axi_slice.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_slice/src/axi_w_buffer.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_slice/src/axi_slice_wrap.sv
