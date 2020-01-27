puts "${Green}Analyzing axi ${NC}"

puts "${Green}--> compile axi${NC}"

analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_pkg.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_address_width_converter.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_demux.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_intf.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_mux.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_perf_mon.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_address_resolver.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_arbiter.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_atop_filter.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_burst_splitter.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_bypass.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_cdc.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_cut.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_data_downsize.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_data_upsize.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_delayer.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_join.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_lite_cut.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_lite_join.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_lite_to_axi.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_modify_address.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_read_burst_buffer.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_to_axi_lite.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_bypass_wrap.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_data_width_converter.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_id_remap.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_lite_multicut.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_lite_xbar.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi/src/axi_multicut.sv

analyze -format sverilog  -work work ${IPS_PATH}/axi_riscv_atomics/src/axi_res_tbl.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi_riscv_atomics/src/axi_riscv_amos_alu.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi_riscv_atomics/src/axi_riscv_amos.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi_riscv_atomics/src/axi_riscv_lrsc.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi_riscv_atomics/src/axi_riscv_atomics.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi_riscv_atomics/src/axi_riscv_lrsc_wrap.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi_riscv_atomics/src/axi_riscv_amos_wrap.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi_riscv_atomics/src/axi_riscv_atomics_wrap.sv

analyze -format sverilog  -work work ${IPS_PATH}/axi2apb/src/axi2apb_wrap.sv
analyze -format sverilog  -work work ${IPS_PATH}/axi2apb/src/axi2apb_64_32.sv
