puts "${Green}Analyzing axi ${NC}"

puts "${Green}--> compile axi${NC}"

analyze -format sv -work work \
    -define { \
        TARGET_SYNOPSYS \
        TARGET_SYNTHESIS \
    } \
    [list \
        "${IPS_PATH}/axi/src/axi_pkg.sv" \
        "${IPS_PATH}/axi/src/axi_intf.sv" \
        "${IPS_PATH}/axi/src/axi_perf_mon.sv" \
        "${IPS_PATH}/axi/src/axi_atop_filter.sv" \
        "${IPS_PATH}/axi/src/axi_cdc.sv" \
        "${IPS_PATH}/axi/src/axi_cut.sv" \
        "${IPS_PATH}/axi/src/axi_data_downsize.sv" \
        "${IPS_PATH}/axi/src/axi_data_upsize.sv" \
        "${IPS_PATH}/axi/src/axi_delayer.sv" \
        "${IPS_PATH}/axi/src/axi_demux.sv" \
        "${IPS_PATH}/axi/src/axi_id_remap.sv" \
        "${IPS_PATH}/axi/src/axi_id_prepend.sv" \
        "${IPS_PATH}/axi/src/axi_join.sv" \
        "${IPS_PATH}/axi/src/axi_lite_demux.sv" \
        "${IPS_PATH}/axi/src/axi_lite_join.sv" \
        "${IPS_PATH}/axi/src/axi_lite_mux.sv" \
        "${IPS_PATH}/axi/src/axi_lite_to_apb.sv" \
        "${IPS_PATH}/axi/src/axi_lite_to_axi.sv" \
        "${IPS_PATH}/axi/src/axi_modify_address.sv" \
        "${IPS_PATH}/axi/src/axi_mux.sv" \
        "${IPS_PATH}/axi/src/axi_read_burst_buffer.sv" \
        "${IPS_PATH}/axi/src/axi_to_axi_lite.sv" \
        "${IPS_PATH}/axi/src/axi_data_width_converter.sv" \
        "${IPS_PATH}/axi/src/axi_decerr_slv.sv" \
        "${IPS_PATH}/axi/src/axi_multicut.sv" \
        "${IPS_PATH}/axi/src/axi_lite_xbar.sv" \
        "${IPS_PATH}/axi/src/axi_xbar.sv" \
    ]

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
