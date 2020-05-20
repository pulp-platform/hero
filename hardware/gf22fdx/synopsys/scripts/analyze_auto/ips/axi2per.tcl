puts "${Green}Analyzing axi2per ${NC}"

puts "${Green}--> compile axi2per${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi2per/axi2per_req_channel.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi2per/axi2per_res_channel.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi2per/axi2per.sv
