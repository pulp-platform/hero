puts "${Green}Analyzing rbe ${NC}"

puts "${Green}--> compile rbe${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_package.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/hwpe_stream_disconnect.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/hwpe_stream_connect.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_accumulators_scm.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_accumulator_quantizor.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_binary_tree.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_binconv_feat_register.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_binconv_sign_register.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_binconv_sop.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_binconv.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_scale.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_stream_mux.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_streamer.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_ctrl_fsm.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_ctrl.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_engine.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_top.sv
analyze -format sverilog  -work work ${IPS_PATH}/rbe/rtl/rbe_top_wrap.sv
