puts "${Green}Analyzing hwpe-ctrl ${NC}"

puts "${Green}--> compile hwpe-ctrl${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/hwpe-ctrl/rtl/hwpe_ctrl_package.sv
analyze -format sverilog  -work work ${IPS_PATH}/hwpe-ctrl/rtl/hwpe_ctrl_interfaces.sv
analyze -format sverilog  -work work ${IPS_PATH}/hwpe-ctrl/rtl/hwpe_ctrl_regfile.sv
analyze -format sverilog  -work work ${IPS_PATH}/hwpe-ctrl/rtl/hwpe_ctrl_regfile_latch.sv
analyze -format sverilog  -work work ${IPS_PATH}/hwpe-ctrl/rtl/hwpe_ctrl_regfile_latch_test_wrap.sv
analyze -format sverilog  -work work ${IPS_PATH}/hwpe-ctrl/rtl/hwpe_ctrl_slave.sv
analyze -format sverilog  -work work ${IPS_PATH}/hwpe-ctrl/rtl/hwpe_ctrl_seq_mult.sv
analyze -format sverilog  -work work ${IPS_PATH}/hwpe-ctrl/rtl/hwpe_ctrl_uloop.sv

