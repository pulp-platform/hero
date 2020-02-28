puts "${Green}Analyzing per2axi ${NC}"

puts "${Green}--> compile per2axi${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/per2axi/src/per2axi_busy_unit.sv
analyze -format sverilog  -work work ${IPS_PATH}/per2axi/src/per2axi_req_channel.sv
analyze -format sverilog  -work work ${IPS_PATH}/per2axi/src/per2axi_res_channel.sv
analyze -format sverilog  -work work ${IPS_PATH}/per2axi/src/per2axi.sv
