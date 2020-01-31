puts "${Green}Analyzing apb_node ${NC}"

puts "${Green}--> compile apb_node${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/apb/apb_node/src/apb_node.sv
analyze -format sverilog  -work work ${IPS_PATH}/apb/apb_node/src/apb_node_wrap.sv
