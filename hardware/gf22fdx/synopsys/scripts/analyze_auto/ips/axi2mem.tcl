puts "${Green}Analyzing axi2mem ${NC}"

puts "${Green}--> compile axi2mem${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/src/mem_to_banks.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/src/axi_to_mem.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/src/axi_to_mem_banked.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/src/axi_to_mem_intf.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/src/axi_to_mem_banked_intf.sv
