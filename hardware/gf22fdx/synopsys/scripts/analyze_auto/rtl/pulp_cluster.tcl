puts "${Green}Analyzing pulp_cluster ${NC}"

puts "${Green}--> compile pulp_cluster${NC}"
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/packages/pulp_cluster_package.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/packages/apu_package.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/core_region.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/core_demux.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/cluster_interconnect_wrap.sv
#analyze -format sverilog  -define INVECAS -work work ${IPS_PATH}/pulp_cluster/rtl/tcdm_banks_wrap.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/per_demux_wrap.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/periph_FIFO.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/cluster_peripherals.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/cluster_clock_gate.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/cluster_timer_wrap.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/cluster_event_map.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/dmac_wrap.sv
#analyze -format sverilog  -define INVECAS -work work ${IPS_PATH}/pulp_cluster/rtl/hwpe_subsystem.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/cluster_bus_wrap.sv
#analyze -format sverilog  -define INVECAS -work work ${IPS_PATH}/pulp_cluster/rtl/axi2mem_wrap.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/axi2per_wrap.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/per2axi_wrap.sv
analyze -format sverilog  -define INVECAS -define TARGET_SYNTHESIS -work work ${IPS_PATH}/pulp_cluster/rtl/pulp_cluster.sv
