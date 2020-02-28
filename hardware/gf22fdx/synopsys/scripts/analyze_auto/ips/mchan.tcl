puts "${Green}Analyzing mchan ${NC}"

puts "${Green}--> compile mchan${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/misc/mchan_arbiter.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/misc/mchan_arb_primitive.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/misc/mchan_rr_flag_req.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ctrl_unit/ctrl_fsm.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ctrl_unit/ctrl_if.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ctrl_unit/ctrl_unit.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ctrl_unit/synch_unit.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ctrl_unit/trans_allocator.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ctrl_unit/trans_queue.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ctrl_unit/trans_arbiter_wrap.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ctrl_unit/trans_unpack.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ctrl_unit/twd_trans_queue.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ctrl_unit/twd_trans_splitter.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ext_unit/ext_ar_buffer.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ext_unit/ext_aw_buffer.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ext_unit/ext_b_buffer.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ext_unit/ext_buffer.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ext_unit/ext_opc_buf.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ext_unit/ext_r_buffer.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ext_unit/ext_rx_if.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ext_unit/ext_tid_gen.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ext_unit/ext_tx_if.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ext_unit/ext_unit.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/ext_unit/ext_w_buffer.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/tcdm_unit/tcdm_cmd_unpack.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/tcdm_unit/tcdm_rx_if.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/tcdm_unit/tcdm_synch.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/tcdm_unit/tcdm_tx_if.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/tcdm_unit/tcdm_unit.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/trans_unit/trans_aligner.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/trans_unit/trans_buffers.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/trans_unit/trans_unit.sv
analyze -format sverilog  -work work ${IPS_PATH}/mchan/./rtl/top/mchan.sv
