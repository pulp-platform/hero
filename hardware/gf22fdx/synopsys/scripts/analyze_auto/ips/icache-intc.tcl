puts "${Green}Analyzing icache-intc ${NC}"

puts "${Green}--> compile icache-intc${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/icache-intc/DistributedArbitrationNetwork_Req_icache_intc.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/icache-intc/DistributedArbitrationNetwork_Resp_icache_intc.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/icache-intc/icache_intc.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/icache-intc/Req_Arb_Node_icache_intc.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/icache-intc/Resp_Arb_Node_icache_intc.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/icache-intc/RoutingBlock_Req_icache_intc.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/icache-intc/RoutingBlock_Resp_icache_intc.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/icache-intc/lint_mux.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/icache-intc/RoutingBlock_2ch_Req_icache_intc.sv
