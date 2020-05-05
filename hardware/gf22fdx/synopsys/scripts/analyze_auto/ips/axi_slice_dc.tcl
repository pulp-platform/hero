puts "${Green}Analyzing axi_slice_dc ${NC}"

puts "${Green}--> compile axi_slice_dc${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/axi_slice_dc/src/axi_slice_dc_master.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi_slice_dc/src/axi_slice_dc_slave.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi_slice_dc/src/dc_data_buffer.sv
analyze -format verilog   -work work ${IPS_PATH}/axi_slice_dc/src/dc_full_detector.v
analyze -format verilog   -work work ${IPS_PATH}/axi_slice_dc/src/dc_synchronizer.v
analyze -format verilog   -work work ${IPS_PATH}/axi_slice_dc/src/dc_token_ring_fifo_din.v
analyze -format verilog   -work work ${IPS_PATH}/axi_slice_dc/src/dc_token_ring_fifo_dout.v
analyze -format verilog   -work work ${IPS_PATH}/axi_slice_dc/src/dc_token_ring.v
analyze -format sverilog  -work work ${IPS_PATH}/axi_slice_dc/src/axi_slice_dc_master_wrap.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi_slice_dc/src/axi_slice_dc_slave_wrap.sv
