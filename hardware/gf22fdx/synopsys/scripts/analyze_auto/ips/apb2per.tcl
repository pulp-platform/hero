puts "${Green}Analyzing apb2per ${NC}"

puts "${Green}--> compile apb2per${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/apb/apb2per/apb2per.sv
