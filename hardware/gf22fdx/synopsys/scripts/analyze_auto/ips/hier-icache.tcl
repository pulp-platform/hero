puts "${Green}Analyzing hier-icache ${NC}"

puts "${Green}--> compile hier-icache${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/RTL/TOP/icache_hier_top.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/RTL/L1_CACHE/pri_icache_controller.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/RTL/L1_CACHE/pri_icache.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/RTL/L1_CACHE/register_file_2r_2w_icache.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/RTL/L1.5_CACHE/AXI4_REFILL_Resp_Deserializer.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/RTL/L1.5_CACHE/share_icache.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/RTL/L1.5_CACHE/icache_controller.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/RTL/L1.5_CACHE/RefillTracker_4.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/RTL/L1.5_CACHE/REP_buffer_4.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/RTL/L1.5_CACHE/ram_ws_rs_data_scm.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/RTL/L1.5_CACHE/ram_ws_rs_tag_scm.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/CTRL_UNIT/hier_icache_ctrl_unit.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/CTRL_UNIT/hier_icache_ctrl_unit_wrap.sv
#analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/huawei/rtl/pulp_soc/rtl/components/pulp_interfaces.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/RTL/TOP/hier_icache_demux.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hier-icache/RTL/TOP/icache128_2_axi64.sv
