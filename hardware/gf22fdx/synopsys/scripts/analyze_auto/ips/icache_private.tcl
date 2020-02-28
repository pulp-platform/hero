puts "${Green}Analyzing icache_private ${NC}"

puts "${Green}--> compile icache-private${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/icache_private/TOP/icache_top_private.sv
analyze -format sverilog  -work work ${IPS_PATH}/icache_private/RTL/ICACHE/icache_bank_private.sv
analyze -format sverilog  -work work ${IPS_PATH}/icache_private/RTL/ICACHE/icache_controller_private.sv
