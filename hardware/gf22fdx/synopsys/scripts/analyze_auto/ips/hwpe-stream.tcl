puts "${Green}Analyzing hwpe-stream ${NC}"

puts "${Green}--> compile hwpe-stream${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/hwpe_stream_package.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/hwpe_stream_interfaces.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/basic/hwpe_stream_assign.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/basic/hwpe_stream_mux_static.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/basic/hwpe_stream_demux_static.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/basic/hwpe_stream_buffer.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/basic/hwpe_stream_merge.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/basic/hwpe_stream_fence.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/basic/hwpe_stream_split.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/fifo/hwpe_stream_fifo_earlystall_sidech.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/fifo/hwpe_stream_fifo_earlystall.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/fifo/hwpe_stream_fifo_scm.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/fifo/hwpe_stream_fifo_scm_test_wrap.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/fifo/hwpe_stream_fifo_sidech.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/fifo/hwpe_stream_fifo.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/fifo/hwpe_stream_fifo_ctrl.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/streamer/hwpe_stream_addressgen.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/streamer/hwpe_stream_strbgen.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/streamer/hwpe_stream_sink.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/streamer/hwpe_stream_sink_realign.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/streamer/hwpe_stream_source.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/streamer/hwpe_stream_source_realign.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/streamer/hwpe_stream_streamer_queue.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/tcdm/hwpe_stream_tcdm_fifo_load.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/tcdm/hwpe_stream_tcdm_fifo_load_sidech.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/tcdm/hwpe_stream_tcdm_fifo_store.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/tcdm/hwpe_stream_tcdm_fifo.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/tcdm/hwpe_stream_tcdm_assign.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/tcdm/hwpe_stream_tcdm_mux.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/tcdm/hwpe_stream_tcdm_mux_static.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/tcdm/hwpe_stream_tcdm_reorder.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/hwpe-stream/rtl/tcdm/hwpe_stream_tcdm_reorder_static.sv


