#!/usr/bin/env bash

# version=vcs-2017.03
version=vcs-2019.06

flags="-nc -full64 -timescale=1ps/1ps -assert svaext "

vcs="${version} vcs ${flags}"
vlogan="${version} vlogan ${flags}"

ROOT=/scratch/sriedel/huawei-2020/hero/hardware

export VCS_HOME=/usr/pack/vcs-2019.06-kgf

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/common_verification/src/clk_rst_gen.sv" \
    "$ROOT/deps/common_verification/src/rand_id_queue.sv" \
    "$ROOT/deps/common_verification/src/rand_stream_mst.sv" \
    "$ROOT/deps/common_verification/src/rand_synch_holdable_driver.sv" \
    "$ROOT/deps/common_verification/src/rand_verif_pkg.sv" \
    "$ROOT/deps/common_verification/src/rand_synch_driver.sv" \
    "$ROOT/deps/common_verification/src/rand_stream_slv.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/tech_cells_generic/src/cluster_clock_gating.sv" \
    "$ROOT/deps/tech_cells_generic/src/pulp_clock_gating.sv" \
    "$ROOT/deps/tech_cells_generic/src/pulp_clock_mux2.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/tech_cells_generic/src/cluster_clock_and2.sv" \
    "$ROOT/deps/tech_cells_generic/src/cluster_clock_buffer.sv" \
    "$ROOT/deps/tech_cells_generic/src/cluster_clock_inverter.sv" \
    "$ROOT/deps/tech_cells_generic/src/cluster_clock_mux2.sv" \
    "$ROOT/deps/tech_cells_generic/src/cluster_clock_xor2.sv" \
    "$ROOT/deps/tech_cells_generic/src/cluster_level_shifter_in.sv" \
    "$ROOT/deps/tech_cells_generic/src/cluster_level_shifter_in_clamp.sv" \
    "$ROOT/deps/tech_cells_generic/src/cluster_level_shifter_inout.sv" \
    "$ROOT/deps/tech_cells_generic/src/cluster_level_shifter_out.sv" \
    "$ROOT/deps/tech_cells_generic/src/cluster_level_shifter_out_clamp.sv" \
    "$ROOT/deps/tech_cells_generic/src/generic_memory.sv" \
    "$ROOT/deps/tech_cells_generic/src/generic_rom.sv" \
    "$ROOT/deps/tech_cells_generic/src/pad_functional.sv" \
    "$ROOT/deps/tech_cells_generic/src/pulp_buffer.sv" \
    "$ROOT/deps/tech_cells_generic/src/pulp_clock_and2.sv" \
    "$ROOT/deps/tech_cells_generic/src/pulp_clock_buffer.sv" \
    "$ROOT/deps/tech_cells_generic/src/pulp_clock_gating_async.sv" \
    "$ROOT/deps/tech_cells_generic/src/pulp_clock_inverter.sv" \
    "$ROOT/deps/tech_cells_generic/src/pulp_clock_xor2.sv" \
    "$ROOT/deps/tech_cells_generic/src/pulp_level_shifter_in.sv" \
    "$ROOT/deps/tech_cells_generic/src/pulp_level_shifter_in_clamp.sv" \
    "$ROOT/deps/tech_cells_generic/src/pulp_level_shifter_out.sv" \
    "$ROOT/deps/tech_cells_generic/src/pulp_level_shifter_out_clamp.sv" \
    "$ROOT/deps/tech_cells_generic/src/pulp_power_gating.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/common_cells/src/cdc_2phase.sv" \
    "$ROOT/deps/common_cells/src/cf_math_pkg.sv" \
    "$ROOT/deps/common_cells/src/clk_div.sv" \
    "$ROOT/deps/common_cells/src/counter.sv" \
    "$ROOT/deps/common_cells/src/edge_propagator_tx.sv" \
    "$ROOT/deps/common_cells/src/fifo_v3.sv" \
    "$ROOT/deps/common_cells/src/graycode.sv" \
    "$ROOT/deps/common_cells/src/lfsr_16bit.sv" \
    "$ROOT/deps/common_cells/src/lfsr_8bit.sv" \
    "$ROOT/deps/common_cells/src/lzc.sv" \
    "$ROOT/deps/common_cells/src/mv_filter.sv" \
    "$ROOT/deps/common_cells/src/onehot_to_bin.sv" \
    "$ROOT/deps/common_cells/src/plru_tree.sv" \
    "$ROOT/deps/common_cells/src/popcount.sv" \
    "$ROOT/deps/common_cells/src/rr_arb_tree.sv" \
    "$ROOT/deps/common_cells/src/rstgen_bypass.sv" \
    "$ROOT/deps/common_cells/src/serial_deglitch.sv" \
    "$ROOT/deps/common_cells/src/shift_reg.sv" \
    "$ROOT/deps/common_cells/src/spill_register.sv" \
    "$ROOT/deps/common_cells/src/stream_demux.sv" \
    "$ROOT/deps/common_cells/src/stream_filter.sv" \
    "$ROOT/deps/common_cells/src/stream_fork.sv" \
    "$ROOT/deps/common_cells/src/stream_join.sv" \
    "$ROOT/deps/common_cells/src/stream_mux.sv" \
    "$ROOT/deps/common_cells/src/sync.sv" \
    "$ROOT/deps/common_cells/src/sync_wedge.sv" \
    "$ROOT/deps/common_cells/src/cdc_fifo_2phase.sv" \
    "$ROOT/deps/common_cells/src/cdc_fifo_gray.sv" \
    "$ROOT/deps/common_cells/src/edge_detect.sv" \
    "$ROOT/deps/common_cells/src/id_queue.sv" \
    "$ROOT/deps/common_cells/src/rstgen.sv" \
    "$ROOT/deps/common_cells/src/stream_delay.sv" \
    "$ROOT/deps/common_cells/src/stream_fifo.sv" \
    "$ROOT/deps/common_cells/src/stream_fork_dynamic.sv" \
    "$ROOT/deps/common_cells/src/fall_through_register.sv" \
    "$ROOT/deps/common_cells/src/mem_to_stream.sv" \
    "$ROOT/deps/common_cells/src/stream_arbiter_flushable.sv" \
    "$ROOT/deps/common_cells/src/stream_register.sv" \
    "$ROOT/deps/common_cells/src/stream_arbiter.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/common_cells/src/sram.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/common_cells/src/deprecated/clock_divider_counter.sv" \
    "$ROOT/deps/common_cells/src/deprecated/fifo_v1.sv" \
    "$ROOT/deps/common_cells/src/deprecated/fifo_v2.sv" \
    "$ROOT/deps/common_cells/src/deprecated/find_first_one.sv" \
    "$ROOT/deps/common_cells/src/deprecated/generic_LFSR_8bit.sv" \
    "$ROOT/deps/common_cells/src/deprecated/generic_fifo.sv" \
    "$ROOT/deps/common_cells/src/deprecated/prioarbiter.sv" \
    "$ROOT/deps/common_cells/src/deprecated/pulp_sync.sv" \
    "$ROOT/deps/common_cells/src/deprecated/pulp_sync_wedge.sv" \
    "$ROOT/deps/common_cells/src/deprecated/rrarbiter.sv" \
    "$ROOT/deps/common_cells/src/deprecated/clock_divider.sv" \
    "$ROOT/deps/common_cells/src/edge_propagator.sv" \
    "$ROOT/deps/common_cells/src/edge_propagator_rx.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/defs_div_sqrt_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/iteration_div_sqrt_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/control_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/norm_div_sqrt_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/preprocess_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/nrbd_nrsc_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/div_sqrt_top_mvp.sv" \
    "$ROOT/deps/fpu_div_sqrt_mvp/hdl/div_sqrt_mvp_wrapper.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/cluster_interconnect/rtl/interfaces/tcdm_bank_mem_bus.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/interfaces/xbar_demux_bus.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/interfaces/xbar_periph_bus.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/interfaces/xbar_tcdm_bus_64.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/interfaces/xbar_tcdm_bus.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "+incdir+$ROOT/deps/cluster_interconnect/rtl/low_latency_interco" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/AddressDecoder_Req.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/AddressDecoder_Resp.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/FanInPrimitive_Req.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/FanInPrimitive_Resp.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/MUX2_REQ.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/TCDM_PIPE_REQ.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/TCDM_PIPE_RESP.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/TestAndSet.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/grant_mask.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/priority_Flag_Req.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/ArbitrationTree.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/ResponseTree.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/RequestBlock1CH.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/RequestBlock2CH.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/ResponseBlock.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/XBAR_TCDM.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/low_latency_interco/XBAR_TCDM_WRAPPER.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "+incdir+$ROOT/deps/cluster_interconnect/rtl/peripheral_interco" \
    "$ROOT/deps/cluster_interconnect/rtl/peripheral_interco/AddressDecoder_PE_Req.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/peripheral_interco/AddressDecoder_Resp_PE.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/peripheral_interco/FanInPrimitive_PE_Resp.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/peripheral_interco/FanInPrimitive_Req_PE.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/peripheral_interco/MUX2_REQ_PE.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/peripheral_interco/RR_Flag_Req_PE.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/peripheral_interco/ArbitrationTree_PE.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/peripheral_interco/ResponseTree_PE.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/peripheral_interco/ResponseBlock_PE.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/peripheral_interco/RequestBlock1CH_PE.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/peripheral_interco/RequestBlock2CH_PE.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/peripheral_interco/XBAR_PE.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/cluster_interconnect/rtl/tcdm_interconnect/tcdm_interconnect_pkg.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/tcdm_interconnect/addr_dec_resp_mux.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/tcdm_interconnect/amo_shim.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/tcdm_interconnect/xbar.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/tcdm_interconnect/clos_net.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/tcdm_interconnect/bfly_net.sv" \
    "$ROOT/deps/cluster_interconnect/rtl/tcdm_interconnect/tcdm_interconnect.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/fpnew/src/fpnew_pkg.sv" \
    "$ROOT/deps/fpnew/src/fpnew_cast_multi.sv" \
    "$ROOT/deps/fpnew/src/fpnew_classifier.sv" \
    "$ROOT/deps/fpnew/src/fpnew_divsqrt_multi.sv" \
    "$ROOT/deps/fpnew/src/fpnew_fma.sv" \
    "$ROOT/deps/fpnew/src/fpnew_fma_multi.sv" \
    "$ROOT/deps/fpnew/src/fpnew_noncomp.sv" \
    "$ROOT/deps/fpnew/src/fpnew_opgroup_block.sv" \
    "$ROOT/deps/fpnew/src/fpnew_opgroup_fmt_slice.sv" \
    "$ROOT/deps/fpnew/src/fpnew_opgroup_multifmt_slice.sv" \
    "$ROOT/deps/fpnew/src/fpnew_rounding.sv" \
    "$ROOT/deps/fpnew/src/fpnew_top.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/axi/src/axi_pkg.sv" \
    "$ROOT/deps/axi/src/axi_address_width_converter.sv" \
    "$ROOT/deps/axi/src/axi_demux.sv" \
    "$ROOT/deps/axi/src/axi_intf.sv" \
    "$ROOT/deps/axi/src/axi_mux.sv" \
    "$ROOT/deps/axi/src/axi_perf_mon.sv" \
    "$ROOT/deps/axi/src/axi_address_resolver.sv" \
    "$ROOT/deps/axi/src/axi_arbiter.sv" \
    "$ROOT/deps/axi/src/axi_atop_filter.sv" \
    "$ROOT/deps/axi/src/axi_burst_splitter.sv" \
    "$ROOT/deps/axi/src/axi_bypass.sv" \
    "$ROOT/deps/axi/src/axi_cdc.sv" \
    "$ROOT/deps/axi/src/axi_cut.sv" \
    "$ROOT/deps/axi/src/axi_data_downsize.sv" \
    "$ROOT/deps/axi/src/axi_data_upsize.sv" \
    "$ROOT/deps/axi/src/axi_delayer.sv" \
    "$ROOT/deps/axi/src/axi_join.sv" \
    "$ROOT/deps/axi/src/axi_lite_cut.sv" \
    "$ROOT/deps/axi/src/axi_lite_join.sv" \
    "$ROOT/deps/axi/src/axi_lite_to_axi.sv" \
    "$ROOT/deps/axi/src/axi_modify_address.sv" \
    "$ROOT/deps/axi/src/axi_read_burst_buffer.sv" \
    "$ROOT/deps/axi/src/axi_to_axi_lite.sv" \
    "$ROOT/deps/axi/src/axi_bypass_wrap.sv" \
    "$ROOT/deps/axi/src/axi_data_width_converter.sv" \
    "$ROOT/deps/axi/src/axi_id_remap.sv" \
    "$ROOT/deps/axi/src/axi_lite_multicut.sv" \
    "$ROOT/deps/axi/src/axi_lite_xbar.sv" \
    "$ROOT/deps/axi/src/axi_multicut.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/axi/src/axi_test.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/axi_slice/src/axi_single_slice.sv" \
    "$ROOT/deps/axi_slice/src/axi_ar_buffer.sv" \
    "$ROOT/deps/axi_slice/src/axi_aw_buffer.sv" \
    "$ROOT/deps/axi_slice/src/axi_b_buffer.sv" \
    "$ROOT/deps/axi_slice/src/axi_r_buffer.sv" \
    "$ROOT/deps/axi_slice/src/axi_slice.sv" \
    "$ROOT/deps/axi_slice/src/axi_w_buffer.sv" \
    "$ROOT/deps/axi_slice/src/axi_slice_wrap.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/cluster_peripherals/cluster_control_unit/cluster_control_unit.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "+incdir+$ROOT/deps/cluster_peripherals/event_unit/include" \
    "$ROOT/deps/cluster_peripherals/event_unit/HW_barrier_logic.sv" \
    "$ROOT/deps/cluster_peripherals/event_unit/event_unit_arbiter.sv" \
    "$ROOT/deps/cluster_peripherals/event_unit/event_unit_mux.sv" \
    "$ROOT/deps/cluster_peripherals/event_unit/event_unit_sm.sv" \
    "$ROOT/deps/cluster_peripherals/event_unit/interrupt_mask.sv" \
    "$ROOT/deps/cluster_peripherals/event_unit/interfaces/bbmux_config_bus.sv" \
    "$ROOT/deps/cluster_peripherals/event_unit/interfaces/clkgate_config_bus.sv" \
    "$ROOT/deps/cluster_peripherals/event_unit/HW_barrier.sv" \
    "$ROOT/deps/cluster_peripherals/event_unit/event_unit_input.sv" \
    "$ROOT/deps/cluster_peripherals/event_unit/event_unit.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/cluster_peripherals/icache_ctrl_unit/interfaces/l0_ctrl_unit_bus.sv" \
    "$ROOT/deps/cluster_peripherals/icache_ctrl_unit/interfaces/mp_icache_ctrl_unit_bus.sv" \
    "$ROOT/deps/cluster_peripherals/icache_ctrl_unit/interfaces/mp_pf_icache_ctrl_unit_bus.sv" \
    "$ROOT/deps/cluster_peripherals/icache_ctrl_unit/interfaces/pri_icache_ctrl_unit_bus.sv" \
    "$ROOT/deps/cluster_peripherals/icache_ctrl_unit/interfaces/sp_icache_ctrl_unit_bus.sv" \
    "$ROOT/deps/cluster_peripherals/icache_ctrl_unit/icache_ctrl_unit.sv" \
    "$ROOT/deps/cluster_peripherals/icache_ctrl_unit/mp_icache_ctrl_unit.sv" \
    "$ROOT/deps/cluster_peripherals/icache_ctrl_unit/mp_pf_icache_ctrl_unit.sv" \
    "$ROOT/deps/cluster_peripherals/icache_ctrl_unit/new_icache_ctrl_unit.sv" \
    "$ROOT/deps/cluster_peripherals/icache_ctrl_unit/pri_icache_ctrl_unit.sv" \
    "$ROOT/deps/cluster_peripherals/icache_ctrl_unit/sp_icache_ctrl_unit.sv" \
    "$ROOT/deps/cluster_peripherals/mmu_config_unit/interfaces/mmu_config_bus.sv" \
    "$ROOT/deps/cluster_peripherals/mmu_config_unit/mmu_config_unit.sv" \
    "$ROOT/deps/cluster_peripherals/perf_counters_unit/perf_counters_unit.sv" \
    "$ROOT/deps/cluster_peripherals/tcdm_pipe_unit/tcdm_pipe_unit.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/icache-intc/Req_Arb_Node_icache_intc.sv" \
    "$ROOT/deps/icache-intc/Resp_Arb_Node_icache_intc.sv" \
    "$ROOT/deps/icache-intc/lint_mux.sv" \
    "$ROOT/deps/icache-intc/DistributedArbitrationNetwork_Req_icache_intc.sv" \
    "$ROOT/deps/icache-intc/DistributedArbitrationNetwork_Resp_icache_intc.sv" \
    "$ROOT/deps/icache-intc/RoutingBlock_Req_icache_intc.sv" \
    "$ROOT/deps/icache-intc/RoutingBlock_2ch_Req_icache_intc.sv" \
    "$ROOT/deps/icache-intc/RoutingBlock_Resp_icache_intc.sv" \
    "$ROOT/deps/icache-intc/icache_intc.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "+incdir+$ROOT/deps/riscv/rtl/include" \
    "$ROOT/deps/riscv/rtl/include/apu_core_package.sv" \
    "$ROOT/deps/riscv/rtl/include/riscv_defines.sv" \
    "$ROOT/deps/riscv/rtl/include/riscv_tracer_defines.sv" \
    "$ROOT/deps/riscv/rtl/register_file_test_wrap.sv" \
    "$ROOT/deps/riscv/rtl/riscv_alu.sv" \
    "$ROOT/deps/riscv/rtl/riscv_alu_basic.sv" \
    "$ROOT/deps/riscv/rtl/riscv_alu_div.sv" \
    "$ROOT/deps/riscv/rtl/riscv_compressed_decoder.sv" \
    "$ROOT/deps/riscv/rtl/riscv_controller.sv" \
    "$ROOT/deps/riscv/rtl/riscv_cs_registers.sv" \
    "$ROOT/deps/riscv/rtl/riscv_decoder.sv" \
    "$ROOT/deps/riscv/rtl/riscv_int_controller.sv" \
    "$ROOT/deps/riscv/rtl/riscv_ex_stage.sv" \
    "$ROOT/deps/riscv/rtl/riscv_hwloop_controller.sv" \
    "$ROOT/deps/riscv/rtl/riscv_hwloop_regs.sv" \
    "$ROOT/deps/riscv/rtl/riscv_id_stage.sv" \
    "$ROOT/deps/riscv/rtl/riscv_if_stage.sv" \
    "$ROOT/deps/riscv/rtl/riscv_load_store_unit.sv" \
    "$ROOT/deps/riscv/rtl/riscv_mult.sv" \
    "$ROOT/deps/riscv/rtl/riscv_pmp.sv" \
    "$ROOT/deps/riscv/rtl/riscv_prefetch_buffer.sv" \
    "$ROOT/deps/riscv/rtl/riscv_prefetch_L0_buffer.sv" \
    "$ROOT/deps/riscv/rtl/riscv_core.sv" \
    "$ROOT/deps/riscv/rtl/riscv_apu_disp.sv" \
    "$ROOT/deps/riscv/rtl/riscv_fetch_fifo.sv" \
    "$ROOT/deps/riscv/rtl/riscv_L0_buffer.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "+incdir+$ROOT/deps/riscv/rtl/include" \
    "$ROOT/deps/riscv/rtl/riscv_register_file.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "+incdir+$ROOT/deps/riscv/rtl/include" \
    "$ROOT/deps/riscv/rtl/include/riscv_defines.sv" \
    "$ROOT/deps/riscv/rtl/include/riscv_tracer_defines.sv" \
    "$ROOT/deps/riscv/rtl/riscv_tracer.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/scm/latch_scm/register_file_1r_1w_test_wrap.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_1w_64b_multi_port_read_32b_1row.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_1w_multi_port_read_1row.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_1r_1w_all.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_1r_1w_all_test_wrap.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_1r_1w_be.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_1r_1w.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_1r_1w_1row.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_1w_128b_multi_port_read_32b.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_1w_64b_multi_port_read_32b.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_1w_64b_1r_32b.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_1w_multi_port_read_be.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_1w_multi_port_read.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_2r_1w_asymm.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_2r_1w_asymm_test_wrap.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_2r_2w.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_3r_2w.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_3r_2w_be.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_multi_way_1w_64b_multi_port_read_32b.sv" \
    "$ROOT/deps/scm/latch_scm/register_file_multi_way_1w_multi_port_read.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/apb/src/apb_intf.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/axi2mem/axi2mem.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/axi2per/axi2per_req_channel.sv" \
    "$ROOT/deps/axi2per/axi2per_res_channel.sv" \
    "$ROOT/deps/axi2per/axi2per.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/axi_node/src/apb_regs_top.sv" \
    "$ROOT/deps/axi_node/src/axi_address_decoder_AR.sv" \
    "$ROOT/deps/axi_node/src/axi_address_decoder_AW.sv" \
    "$ROOT/deps/axi_node/src/axi_address_decoder_BR.sv" \
    "$ROOT/deps/axi_node/src/axi_address_decoder_BW.sv" \
    "$ROOT/deps/axi_node/src/axi_address_decoder_DW.sv" \
    "$ROOT/deps/axi_node/src/axi_node_arbiter.sv" \
    "$ROOT/deps/axi_node/src/axi_AR_allocator.sv" \
    "$ROOT/deps/axi_node/src/axi_AW_allocator.sv" \
    "$ROOT/deps/axi_node/src/axi_BR_allocator.sv" \
    "$ROOT/deps/axi_node/src/axi_BW_allocator.sv" \
    "$ROOT/deps/axi_node/src/axi_DW_allocator.sv" \
    "$ROOT/deps/axi_node/src/axi_multiplexer.sv" \
    "$ROOT/deps/axi_node/src/axi_node.sv" \
    "$ROOT/deps/axi_node/src/axi_node_intf_wrap.sv" \
    "$ROOT/deps/axi_node/src/axi_node_wrap_with_slices.sv" \
    "$ROOT/deps/axi_node/src/axi_regs_top.sv" \
    "$ROOT/deps/axi_node/src/axi_request_block.sv" \
    "$ROOT/deps/axi_node/src/axi_response_block.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/axi_slice_dc/src/axi_slice_dc_master.sv" \
    "$ROOT/deps/axi_slice_dc/src/axi_slice_dc_slave.sv" \
    "$ROOT/deps/axi_slice_dc/src/dc_data_buffer.sv" \
    "$ROOT/deps/axi_slice_dc/src/dc_full_detector.v" \
    "$ROOT/deps/axi_slice_dc/src/dc_synchronizer.v" \
    "$ROOT/deps/axi_slice_dc/src/dc_token_ring_fifo_din.v" \
    "$ROOT/deps/axi_slice_dc/src/dc_token_ring_fifo_dout.v" \
    "$ROOT/deps/axi_slice_dc/src/dc_token_ring.v" \
    "$ROOT/deps/axi_slice_dc/src/axi_slice_dc_master_wrap.sv" \
    "$ROOT/deps/axi_slice_dc/src/axi_slice_dc_slave_wrap.sv" \
    "$ROOT/deps/axi_slice_dc/src/axi_cdc.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "+incdir+$ROOT/deps/event_unit_flex/./rtl" \
    "$ROOT/deps/event_unit_flex/rtl/event_unit_core.sv" \
    "$ROOT/deps/event_unit_flex/rtl/event_unit_interface_mux.sv" \
    "$ROOT/deps/event_unit_flex/rtl/event_unit_top.sv" \
    "$ROOT/deps/event_unit_flex/rtl/soc_periph_fifo.sv" \
    "$ROOT/deps/event_unit_flex/rtl/interc_sw_evt_trig.sv" \
    "$ROOT/deps/event_unit_flex/rtl/hw_barrier_unit.sv" \
    "$ROOT/deps/event_unit_flex/rtl/hw_mutex_unit.sv" \
    "$ROOT/deps/event_unit_flex/rtl/hw_dispatch.sv" \
    "$ROOT/deps/event_unit_flex/rtl/periph_FIFO_id.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/fpga-support/rtl/AxiToAxiLitePc.sv" \
    "$ROOT/deps/fpga-support/rtl/BramPort.sv" \
    "$ROOT/deps/fpga-support/rtl/SyncDpRam.sv" \
    "$ROOT/deps/fpga-support/rtl/SyncSpRam.sv" \
    "$ROOT/deps/fpga-support/rtl/SyncSpRamBeNx32.sv" \
    "$ROOT/deps/fpga-support/rtl/SyncSpRamBeNx64.sv" \
    "$ROOT/deps/fpga-support/rtl/SyncTpRam.sv" \
    "$ROOT/deps/fpga-support/rtl/BramDwc.sv" \
    "$ROOT/deps/fpga-support/rtl/TdpBramArray.sv" \
    "$ROOT/deps/fpga-support/rtl/BramLogger.sv" \
    "$ROOT/deps/fpga-support/rtl/AxiBramLogger.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "+incdir+$ROOT/deps/fpu_interco/../riscv/rtl/include" \
    "$ROOT/deps/fpu_interco/../riscv/rtl/include/riscv_defines.sv" \
    "$ROOT/deps/fpu_interco/FP_WRAP/fp_iter_divsqrt_msv_wrapper_2_STAGE.sv" \
    "$ROOT/deps/fpu_interco/FP_WRAP/fpnew_wrapper.sv" \
    "$ROOT/deps/fpu_interco/RTL/AddressDecoder_Req_FPU.sv" \
    "$ROOT/deps/fpu_interco/RTL/AddressDecoder_Resp_FPU.sv" \
    "$ROOT/deps/fpu_interco/RTL/ArbitrationTree_FPU.sv" \
    "$ROOT/deps/fpu_interco/RTL/FanInPrimitive_Req_FPU.sv" \
    "$ROOT/deps/fpu_interco/RTL/FanInPrimitive_Resp_FPU.sv" \
    "$ROOT/deps/fpu_interco/RTL/optimal_alloc.sv" \
    "$ROOT/deps/fpu_interco/RTL/FPU_clock_gating.sv" \
    "$ROOT/deps/fpu_interco/RTL/LFSR_FPU.sv" \
    "$ROOT/deps/fpu_interco/RTL/RequestBlock_FPU.sv" \
    "$ROOT/deps/fpu_interco/RTL/ResponseBlock_FPU.sv" \
    "$ROOT/deps/fpu_interco/RTL/ResponseTree_FPU.sv" \
    "$ROOT/deps/fpu_interco/RTL/RR_Flag_Req_FPU.sv" \
    "$ROOT/deps/fpu_interco/RTL/shared_fpu_cluster.sv" \
    "$ROOT/deps/fpu_interco/RTL/fpu_demux.sv" \
    "$ROOT/deps/fpu_interco/RTL/XBAR_FPU.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/hier-icache/RTL/TOP/icache_hier_top.sv" \
    "$ROOT/deps/hier-icache/RTL/L1_CACHE/pri_icache_controller.sv" \
    "$ROOT/deps/hier-icache/RTL/L1_CACHE/pri_icache.sv" \
    "$ROOT/deps/hier-icache/RTL/L1.5_CACHE/AXI4_REFILL_Resp_Deserializer.sv" \
    "$ROOT/deps/hier-icache/RTL/L1.5_CACHE/share_icache.sv" \
    "$ROOT/deps/hier-icache/RTL/L1.5_CACHE/icache_controller.sv" \
    "$ROOT/deps/hier-icache/RTL/L1.5_CACHE/RefillTracker_4.sv" \
    "$ROOT/deps/hier-icache/RTL/L1.5_CACHE/REP_buffer_4.sv" \
    "$ROOT/deps/hier-icache/RTL/L1.5_CACHE/ram_ws_rs_data_scm.sv" \
    "$ROOT/deps/hier-icache/RTL/L1.5_CACHE/ram_ws_rs_tag_scm.sv" \
    "$ROOT/deps/hier-icache/CTRL_UNIT/hier_icache_ctrl_unit.sv" \
    "$ROOT/deps/hier-icache/CTRL_UNIT/hier_icache_ctrl_unit_wrap.sv" \
    "$ROOT/deps/hier-icache/RTL/TOP/hier_icache_demux.sv" \
    "$ROOT/deps/hier-icache/RTL/TOP/icache128_2_axi64.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/icache_mp_128_pf/RTL/icache_bank_mp_128.sv" \
    "$ROOT/deps/icache_mp_128_pf/RTL/icache_bank_mp_PF.sv" \
    "$ROOT/deps/icache_mp_128_pf/RTL/merge_refill_cam_128_16.sv" \
    "$ROOT/deps/icache_mp_128_pf/RTL/pf_miss_mux.sv" \
    "$ROOT/deps/icache_mp_128_pf/RTL/prefetcher_if.sv" \
    "$ROOT/deps/icache_mp_128_pf/RTL/central_controller_128.sv" \
    "$ROOT/deps/icache_mp_128_pf/RTL/cache_controller_to_axi_128_PF.sv" \
    "$ROOT/deps/icache_mp_128_pf/RTL/icache_top_mp_128_PF.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "+incdir+$ROOT/deps/mchan/rtl/include" \
    "$ROOT/deps/mchan/rtl/misc/mchan_arbiter.sv" \
    "$ROOT/deps/mchan/rtl/misc/mchan_arb_primitive.sv" \
    "$ROOT/deps/mchan/rtl/misc/mchan_rr_flag_req.sv" \
    "$ROOT/deps/mchan/rtl/ctrl_unit/ctrl_fsm.sv" \
    "$ROOT/deps/mchan/rtl/ctrl_unit/ctrl_if.sv" \
    "$ROOT/deps/mchan/rtl/ctrl_unit/ctrl_unit.sv" \
    "$ROOT/deps/mchan/rtl/ctrl_unit/synch_unit.sv" \
    "$ROOT/deps/mchan/rtl/ctrl_unit/trans_allocator.sv" \
    "$ROOT/deps/mchan/rtl/ctrl_unit/trans_queue.sv" \
    "$ROOT/deps/mchan/rtl/ctrl_unit/trans_arbiter_wrap.sv" \
    "$ROOT/deps/mchan/rtl/ctrl_unit/trans_unpack.sv" \
    "$ROOT/deps/mchan/rtl/ctrl_unit/twd_trans_queue.sv" \
    "$ROOT/deps/mchan/rtl/ctrl_unit/twd_trans_splitter.sv" \
    "$ROOT/deps/mchan/rtl/ext_unit/ext_ar_buffer.sv" \
    "$ROOT/deps/mchan/rtl/ext_unit/ext_aw_buffer.sv" \
    "$ROOT/deps/mchan/rtl/ext_unit/ext_b_buffer.sv" \
    "$ROOT/deps/mchan/rtl/ext_unit/ext_buffer.sv" \
    "$ROOT/deps/mchan/rtl/ext_unit/ext_opc_buf.sv" \
    "$ROOT/deps/mchan/rtl/ext_unit/ext_r_buffer.sv" \
    "$ROOT/deps/mchan/rtl/ext_unit/ext_rx_if.sv" \
    "$ROOT/deps/mchan/rtl/ext_unit/ext_tid_gen.sv" \
    "$ROOT/deps/mchan/rtl/ext_unit/ext_tx_if.sv" \
    "$ROOT/deps/mchan/rtl/ext_unit/ext_unit.sv" \
    "$ROOT/deps/mchan/rtl/ext_unit/ext_w_buffer.sv" \
    "$ROOT/deps/mchan/rtl/tcdm_unit/tcdm_cmd_unpack.sv" \
    "$ROOT/deps/mchan/rtl/tcdm_unit/tcdm_rx_if.sv" \
    "$ROOT/deps/mchan/rtl/tcdm_unit/tcdm_synch.sv" \
    "$ROOT/deps/mchan/rtl/tcdm_unit/tcdm_tx_if.sv" \
    "$ROOT/deps/mchan/rtl/tcdm_unit/tcdm_unit.sv" \
    "$ROOT/deps/mchan/rtl/trans_unit/trans_aligner.sv" \
    "$ROOT/deps/mchan/rtl/trans_unit/trans_buffers.sv" \
    "$ROOT/deps/mchan/rtl/trans_unit/trans_unit.sv" \
    "$ROOT/deps/mchan/rtl/top/mchan.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/per2axi/src/per2axi_busy_unit.sv" \
    "$ROOT/deps/per2axi/src/per2axi_req_channel.sv" \
    "$ROOT/deps/per2axi/src/per2axi_res_channel.sv" \
    "$ROOT/deps/per2axi/src/per2axi.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/timer_unit/rtl/timer_unit_counter.sv" \
    "$ROOT/deps/timer_unit/rtl/timer_unit_counter_presc.sv" \
    "$ROOT/deps/timer_unit/rtl/apb_timer_unit.sv" \
    "$ROOT/deps/timer_unit/rtl/timer_unit.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/axi2apb/src/axi2apb.sv" \
    "$ROOT/deps/axi2apb/src/axi2apb_64_32.sv" \
    "$ROOT/deps/axi2apb/src/axi2apb_wrap.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/axi_rab/rtl/axi4_ar_sender.sv" \
    "$ROOT/deps/axi_rab/rtl/axi4_aw_sender.sv" \
    "$ROOT/deps/axi_rab/rtl/axi4_b_sender.sv" \
    "$ROOT/deps/axi_rab/rtl/axi4_r_sender.sv" \
    "$ROOT/deps/axi_rab/rtl/axi4_w_buffer.sv" \
    "$ROOT/deps/axi_rab/rtl/axi4_w_sender.sv" \
    "$ROOT/deps/axi_rab/rtl/axi_buffer_rab_bram.sv" \
    "$ROOT/deps/axi_rab/rtl/axi_rab_cfg.sv" \
    "$ROOT/deps/axi_rab/rtl/axi_rab_top.sv" \
    "$ROOT/deps/axi_rab/rtl/check_ram.sv" \
    "$ROOT/deps/axi_rab/rtl/fsm.sv" \
    "$ROOT/deps/axi_rab/rtl/l2_tlb.sv" \
    "$ROOT/deps/axi_rab/rtl/rab_core.sv" \
    "$ROOT/deps/axi_rab/rtl/rab_slice.sv" \
    "$ROOT/deps/axi_rab/rtl/ram_tp_write_first.sv" \
    "$ROOT/deps/axi_rab/rtl/ram_tp_no_change.sv" \
    "$ROOT/deps/axi_rab/rtl/slice_top.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_res_tbl.sv" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_riscv_amos_alu.sv" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_riscv_amos.sv" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_riscv_lrsc.sv" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_riscv_atomics.sv" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_riscv_lrsc_wrap.sv" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_riscv_amos_wrap.sv" \
    "$ROOT/deps/axi_riscv_atomics/src/axi_riscv_atomics_wrap.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/axi_riscv_atomics/test/generic_memory.sv" \
    "$ROOT/deps/axi_riscv_atomics/test/axi_memory.sv" \
    "$ROOT/deps/axi_riscv_atomics/test/tb_axi_pkg.sv" \
    "$ROOT/deps/axi_riscv_atomics/test/golden_memory.sv" \
    "$ROOT/deps/axi_riscv_atomics/test/tb_top.sv" \
    "$ROOT/deps/axi_riscv_atomics/test/axi_riscv_lrsc_tb.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/deps/pulp_cluster/packages/pulp_cluster_package.sv" \
    "$ROOT/deps/pulp_cluster/packages/apu_package.sv" \
    "$ROOT/deps/pulp_cluster/rtl/axi2per_wrap.sv" \
    "$ROOT/deps/pulp_cluster/rtl/axi_slice_wrap.sv" \
    "$ROOT/deps/pulp_cluster/rtl/cluster_bus_wrap.sv" \
    "$ROOT/deps/pulp_cluster/rtl/cluster_clock_gate.sv" \
    "$ROOT/deps/pulp_cluster/rtl/cluster_event_map.sv" \
    "$ROOT/deps/pulp_cluster/rtl/cluster_interconnect_wrap.sv" \
    "$ROOT/deps/pulp_cluster/rtl/cluster_timer_wrap.sv" \
    "$ROOT/deps/pulp_cluster/rtl/dmac_wrap.sv" \
    "$ROOT/deps/pulp_cluster/rtl/per2axi_wrap.sv" \
    "$ROOT/deps/pulp_cluster/rtl/per_demux_wrap.sv" \
    "$ROOT/deps/pulp_cluster/rtl/periph_FIFO.sv" \
    "$ROOT/deps/pulp_cluster/rtl/periph_demux.sv" \
    "$ROOT/deps/pulp_cluster/rtl/cluster_peripherals.sv" \
    "$ROOT/deps/pulp_cluster/rtl/core_demux.sv" \
    "$ROOT/deps/pulp_cluster/rtl/core_region.sv" \
    "$ROOT/deps/pulp_cluster/rtl/pulp_cluster.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/src/apb/apb_bus.sv" \
    "$ROOT/src/apb/apb_ro_regs.sv" \
    "$ROOT/src/apb/apb_rw_regs.sv" \
    "$ROOT/src/apb/apb_bus_wrap.sv" \
    "$ROOT/src/axi_rab_wrap.sv" \
    "$ROOT/src/pulp_cluster_cfg_pkg.sv" \
    "$ROOT/src/soc_bus.sv" \
    "$ROOT/src/soc_ctrl_regs.sv" \
    "$ROOT/src/sram.sv" \
    "$ROOT/src/l2_mem.sv" \
    "$ROOT/src/pulp_cluster_ooc.sv" \
    "$ROOT/src/soc_peripherals.sv" \
    "$ROOT/src/pulp.sv" \
    "$ROOT/src/pulp_ooc.sv"

${vlogan} -sverilog \
    +define+TARGET_RTL \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/deps/common_cells/include" \
    "+incdir+$ROOT/deps/axi/include" \
    "+incdir+$ROOT/src/apb/include" \
    "$ROOT/src/apb/apb_stdout.sv" \
    "$ROOT/test/pulp_tb.sv"
