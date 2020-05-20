puts "${Green}Analyzing cluster_peripherals ${NC}"

puts "${Green}--> compile cluster_control_unit${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/cluster_control_unit/cluster_control_unit.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/icache_ctrl_unit/interfaces/sp_icache_ctrl_unit_bus.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/icache_ctrl_unit/interfaces/pri_icache_ctrl_unit_bus.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/icache_ctrl_unit/interfaces/l0_ctrl_unit_bus.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/icache_ctrl_unit/interfaces/mp_icache_ctrl_unit_bus.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/icache_ctrl_unit/interfaces/mp_pf_icache_ctrl_unit_bus.sv

puts "${Green}--> compile event_unit${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/event_unit/event_unit_arbiter.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/event_unit/event_unit_input.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/event_unit/event_unit_mux.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/event_unit/event_unit_sm.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/event_unit/event_unit.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/event_unit/HW_barrier_logic.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/event_unit/HW_barrier.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/event_unit/interrupt_mask.sv

puts "${Green}--> compile icache_ctrl_unit${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/icache_ctrl_unit/icache_ctrl_unit.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/icache_ctrl_unit/new_icache_ctrl_unit.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/icache_ctrl_unit/mp_icache_ctrl_unit.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/icache_ctrl_unit/sp_icache_ctrl_unit.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/icache_ctrl_unit/pri_icache_ctrl_unit.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/icache_ctrl_unit/mp_pf_icache_ctrl_unit.sv

puts "${Green}--> compile mmu_config_unit${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/mmu_config_unit/mmu_config_unit.sv

puts "${Green}--> compile perf_counters_unit${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/perf_counters_unit/perf_counters_unit.sv

puts "${Green}--> compile tcdm_pipe_unit${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/cluster_peripherals/tcdm_pipe_unit/tcdm_pipe_unit.sv
