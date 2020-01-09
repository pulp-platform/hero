
rm -rf work

#Dependancies!!!!
set REPO_PATH="../RTL"

cd ../RTL
git clone git@iis-git.ee.ethz.ch:pulp-open/axi_node.git --branch v1.0.1
git clone git@github.com:pulp-platform/axi_slice.git --branch v1.1.0
git clone git@github.com:pulp-platform/common_cells.git --branch v1.10.0
git clone git@github.com:pulp-platform/tech_cells_generic.git
cd tech_cells_generic
git checkout 812f60a4a46
cd ..
git clone git@github.com:pulp-platform/icache-intc.git --branch pulp-v1.0
git clone git@github.com:pulp-platform/scm.git --branch v1.0.0
cd ../SIM

# COMPILE THE RTL
 vlog -quiet -sv ../RTL/TOP/icache_hier_top.sv
 vlog -quiet -sv ../RTL/TOP/hier_icache_demux.sv
 vlog -quiet -sv ../RTL/TOP/icache128_2_axi64.sv

 vlog -quiet -sv ../RTL/L1_CACHE/pri_icache_controller.sv
 vlog -quiet -sv ../RTL/L1_CACHE/pri_icache.sv

 vlog -quiet -sv ../RTL/L1.5_CACHE/AXI4_REFILL_Resp_Deserializer.sv
 vlog -quiet -sv ../RTL/L1.5_CACHE/share_icache.sv
 vlog -quiet -sv ../RTL/L1.5_CACHE/icache_controller.sv
 vlog -quiet -sv ../RTL/L1.5_CACHE/RefillTracker_4.sv
 vlog -quiet -sv ../RTL/L1.5_CACHE/REP_buffer_4.sv
 vlog -quiet -sv ../RTL/L1.5_CACHE/ram_ws_rs_data_scm.sv +define+USE_SRAM
 vlog -quiet -sv ../RTL/L1.5_CACHE/ram_ws_rs_tag_scm.sv  +define+USE_SRAM




 # COMPILE RTL from other Repositories
 vlog -sv -work work -quiet ../RTL/axi_node/axi_address_decoder_AR.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_address_decoder_AW.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_address_decoder_BR.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_address_decoder_BW.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_address_decoder_DW.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_ArbitrationTree.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_AR_allocator.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_AW_allocator.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_BR_allocator.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_BW_allocator.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_DW_allocator.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_FanInPrimitive_Req.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_multiplexer.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_regs_top.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_node_wrap_with_slices.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_node_wrap.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_node.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_request_block.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_response_block.sv
 vlog -sv -work work -quiet ../RTL/axi_node/axi_RR_Flag_Req.sv



 vlog -sv -work work -quiet ../RTL/axi_slice/axi_r_buffer.sv
 vlog -sv -work work -quiet ../RTL/axi_slice/axi_ar_buffer.sv
 vlog -sv -work work -quiet ../RTL/axi_slice/axi_aw_buffer.sv
 vlog -sv -work work -quiet ../RTL/axi_slice/axi_w_buffer.sv
 vlog -sv -work work -quiet ../RTL/axi_slice/axi_b_buffer.sv
 vlog -sv -work work -quiet ../RTL/axi_slice/axi_buffer.sv


 vlog -sv -work work -quiet ../RTL/common_cells/src/fifo_v3.sv
 vlog -sv -work work -quiet ../RTL/common_cells/src/fifo_v2.sv
 vlog -sv -work work -quiet ../RTL/common_cells/src/deprecated/generic_fifo.sv
 vlog -sv -work work -quiet ../RTL/common_cells/src/lfsr_8bit.sv
 vlog -sv -work work -quiet ../RTL/common_cells/src/onehot_to_bin.sv

 vlog -sv -work work -quiet ../RTL/tech_cells_generic/src/cluster_clock_gating.sv

 vlog -sv -work work -quiet ../RTL/icache-intc/DistributedArbitrationNetwork_Req_icache_intc.sv
 vlog -sv -work work -quiet ../RTL/icache-intc/DistributedArbitrationNetwork_Resp_icache_intc.sv
 vlog -sv -work work -quiet ../RTL/icache-intc/icache_intc.sv
 vlog -sv -work work -quiet ../RTL/icache-intc/Req_Arb_Node_icache_intc.sv
 vlog -sv -work work -quiet ../RTL/icache-intc/Resp_Arb_Node_icache_intc.sv
 vlog -sv -work work -quiet ../RTL/icache-intc/RoutingBlock_Req_icache_intc.sv
 vlog -sv -work work -quiet ../RTL/icache-intc/RoutingBlock_2ch_Req_icache_intc.sv
 vlog -sv -work work -quiet ../RTL/icache-intc/RoutingBlock_Resp_icache_intc.sv
 vlog -sv -work work -quiet ../RTL/icache-intc/lint_mux.sv

 vlog -sv -work work -quiet ../RTL/scm/latch_scm/register_file_1r_1w_test_wrap.sv
 vlog -sv -work work -quiet ../RTL/scm/latch_scm/register_file_1r_1w.sv


 # COMPILE TB STUFF
 vlog -sv -work work -quiet  ../TB/axi_mem_if.sv
 vlog -sv -work work -quiet  ../TB/ibus_lint_memory_128.sv
 vlog -sv -work work -quiet  ../TB/l2_generic.sv
 vlog -sv -work work -quiet  ../TB/tgen_128.sv
 vlog -sv -work work -quiet  ../TB/generic_memory_with_grant.sv
 vlog -sv -work work -quiet  ../TB/tb.sv

 # vlog -sv -work work SRAM_SP_32w_10b_SS_1V08_125c.v  +define+FUNCTIONAL
 # vlog -sv -work work SRAM_SP_32w_128b_SS_1V08_125c.v +define+FUNCTIONAL

 vopt +acc tb -o tb_no_opt
 vsim tb_no_opt -do "do wave.do; run 10us; source enable_icache_no_prefetch.tcl; run 1ms; q"


# To enable the ICACHES
# force -freeze sim:/tb/sh_req_disable   9'b00000_0000 0
# force -freeze sim:/tb/sh_req_enable    9'b11111_1111 0
# force -freeze sim:/tb/pri_bypass_req   9'b00000_0000 0
# force -freeze sim:/tb/enable_l1_l15_prefetch   9'b11111_1111 0
# force -freeze sim:/tb/special_core_icache      1'b0 0
# run 1ms
