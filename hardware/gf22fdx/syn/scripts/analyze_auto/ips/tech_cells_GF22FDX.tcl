puts "${Green}Analyzing tech_cells_GF22FDX ${NC}"

puts "${Green}--> compile tech_cells_GF22FDX${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/tech_cells_GF22FDX/pulp_power_gating_gf22.sv
analyze -format sverilog  -work work ${IPS_PATH}/tech_cells_GF22FDX/cluster_clock_inverter_gf22.sv
analyze -format sverilog  -work work ${IPS_PATH}/tech_cells_GF22FDX/cluster_clock_gating_gf22.sv
analyze -format sverilog  -work work ${IPS_PATH}/tech_cells_GF22FDX/pulp_clock_delay_gf22.sv
analyze -format sverilog  -work work ${IPS_PATH}/tech_cells_GF22FDX/pulp_clock_gating_gf22.sv
analyze -format sverilog  -work work ${IPS_PATH}/tech_cells_GF22FDX/pulp_clock_inverter_gf22.sv
analyze -format sverilog  -work work ${IPS_PATH}/tech_cells_GF22FDX/pulp_clock_mux2_gf22.sv
analyze -format sverilog  -work work ${IPS_PATH}/tech_cells_GF22FDX/pulp_clock_xor2_gf22.sv
analyze -format sverilog  -work work ${IPS_PATH}/tech_cells_GF22FDX/pulp_sync_gf22.sv
analyze -format sverilog  -work work ${IPS_PATH}/tech_cells_GF22FDX/pulp_clock_gating_async_gf22.sv

puts "${Green}--> compile r2p_wrappers_GF22FDX${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/tech_cells_GF22FDX/CCI_FIFO_64w_8b_wrap.sv
analyze -format sverilog  -work work ${IPS_PATH}/tech_cells_GF22FDX/DATA_FIFO_2048w_64b_wrap.sv
analyze -format sverilog  -work work ${IPS_PATH}/tech_cells_GF22FDX/LANE_FIFO_16w_64b_wrap.sv
