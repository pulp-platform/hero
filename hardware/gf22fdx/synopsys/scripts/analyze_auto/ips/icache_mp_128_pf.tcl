puts "${Green}Analyzing icache_mp_128_pf ${NC}"

puts "${Green}--> compile icache_mp_128_pf${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/icache_mp_128_pf/RTL/cache_controller_to_axi_128_PF.sv
analyze -format sverilog  -work work ${IPS_PATH}/icache_mp_128_pf/RTL/central_controller_128.sv
analyze -format sverilog  -work work ${IPS_PATH}/icache_mp_128_pf/RTL/icache_bank_mp_128.sv
analyze -format sverilog  -work work ${IPS_PATH}/icache_mp_128_pf/RTL/icache_bank_mp_PF.sv
analyze -format sverilog  -work work ${IPS_PATH}/icache_mp_128_pf/RTL/icache_top_mp_128_PF.sv
analyze -format sverilog  -work work ${IPS_PATH}/icache_mp_128_pf/RTL/merge_refill_cam_128_16.sv
analyze -format sverilog  -work work ${IPS_PATH}/icache_mp_128_pf/RTL/pf_miss_mux.sv
analyze -format sverilog  -work work ${IPS_PATH}/icache_mp_128_pf/RTL/prefetcher_if.sv
