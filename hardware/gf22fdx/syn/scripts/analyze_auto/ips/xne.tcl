puts "${Green}Analyzing xne ${NC}"

puts "${Green}--> compile xne${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/xne/rtl/xne_package.sv
analyze -format sverilog  -work work ${IPS_PATH}/xne/rtl/xne_accumulators_scm.sv
analyze -format sverilog  -work work ${IPS_PATH}/xne/rtl/xne_feat_register.sv
analyze -format sverilog  -work work ${IPS_PATH}/xne/rtl/xne_sop.sv
analyze -format sverilog  -work work ${IPS_PATH}/xne/rtl/xne_engine.sv
analyze -format sverilog  -work work ${IPS_PATH}/xne/rtl/xne_streamer.sv
analyze -format sverilog  -work work ${IPS_PATH}/xne/rtl/xne_ctrl.sv
analyze -format sverilog  -work work ${IPS_PATH}/xne/rtl/xne_ctrl_fsm.sv
analyze -format sverilog  -work work ${IPS_PATH}/xne/rtl/xne_top.sv
analyze -format sverilog  -work work ${IPS_PATH}/xne/wrap/xne_engine_wrap.sv
analyze -format sverilog  -work work ${IPS_PATH}/xne/wrap/xne_streamer_wrap.sv
analyze -format sverilog  -work work ${IPS_PATH}/xne/wrap/xne_top_wrap.sv
