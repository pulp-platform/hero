puts "${Green}Analyzing common_cells ${NC}"

puts "${Green}--> compile common_cells_all${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/cdc_2phase.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/clk_div.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/counter.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/edge_propagator_tx.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/fifo_v3.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/lfsr_8bit.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/lzc.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/mv_filter.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/onehot_to_bin.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/plru_tree.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/popcount.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/rr_arb_tree.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/rstgen_bypass.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/serial_deglitch.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/shift_reg.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/spill_register.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/stream_demux.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/stream_filter.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/stream_fork.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/stream_mux.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/stream_fifo.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/sync.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/sync_wedge.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/edge_detect.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/id_queue.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/rstgen.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/stream_delay.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/fall_through_register.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/stream_arbiter_flushable.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/stream_register.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/stream_arbiter.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/deprecated/clock_divider_counter.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/deprecated/find_first_one.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/deprecated/generic_LFSR_8bit.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/deprecated/generic_fifo.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/deprecated/generic_fifo_adv.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/deprecated/pulp_sync.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/deprecated/pulp_sync_wedge.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/deprecated/clock_divider.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/deprecated/fifo_v2.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/deprecated/prioarbiter.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/deprecated/rrarbiter.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/deprecated/fifo_v1.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/edge_propagator.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/edge_propagator_rx.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/cf_math_pkg.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/mem_to_stream.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/stream_join.sv
analyze -format sverilog  -work work ${IPS_PATH}/common_cells/src/stream_fork_dynamic.sv
