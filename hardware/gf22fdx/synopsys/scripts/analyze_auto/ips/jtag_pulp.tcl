puts "${Green}Analyzing jtag_pulp ${NC}"

puts "${Green}--> compile jtag_pulp${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/jtag_pulp/src/bscell.sv
analyze -format sverilog  -work work ${IPS_PATH}/jtag_pulp/src/jtag_axi_wrap.sv
analyze -format sverilog  -work work ${IPS_PATH}/jtag_pulp/src/jtag_enable.sv
analyze -format sverilog  -work work ${IPS_PATH}/jtag_pulp/src/jtag_enable_synch.sv
analyze -format sverilog  -work work ${IPS_PATH}/jtag_pulp/src/jtagreg.sv
analyze -format sverilog  -work work ${IPS_PATH}/jtag_pulp/src/jtag_rst_synch.sv
analyze -format sverilog  -work work ${IPS_PATH}/jtag_pulp/src/jtag_sync.sv
analyze -format verilog   -work work ${IPS_PATH}/jtag_pulp/src/tap_top.v
