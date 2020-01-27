puts "${Green}Analyzing axi2mem ${NC}"

puts "${Green}--> compile axi2mem${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/axi2mem_busy_unit.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/axi2mem_rd_channel.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/axi2mem.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/axi2mem_tcdm_rd_if.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/axi2mem_tcdm_synch.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/axi2mem_tcdm_unit.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/axi2mem_tcdm_wr_if.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/axi2mem_trans_unit.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi2mem/axi2mem_wr_channel.sv
