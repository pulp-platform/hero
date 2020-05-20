puts "${Green}Analyzing L2_tcdm_hybrid_interco ${NC}"

puts "${Green}--> compile soc_interconnect${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/l2_tcdm_demux.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/lint_2_apb.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/lint_2_axi.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/axi_2_lint/axi64_2_lint32.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/axi_2_lint/axi_read_ctrl.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/axi_2_lint/axi_write_ctrl.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/axi_2_lint/lint64_to_32.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_L2/AddressDecoder_Req_L2.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_L2/AddressDecoder_Resp_L2.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_L2/ArbitrationTree_L2.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_L2/FanInPrimitive_Req_L2.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_L2/FanInPrimitive_Resp_L2.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_L2/MUX2_REQ_L2.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_L2/RequestBlock_L2_1CH.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_L2/RequestBlock_L2_2CH.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_L2/ResponseBlock_L2.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_L2/ResponseTree_L2.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_L2/RR_Flag_Req_L2.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_L2/XBAR_L2.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_BRIDGE/AddressDecoder_Req_BRIDGE.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_BRIDGE/AddressDecoder_Resp_BRIDGE.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_BRIDGE/ArbitrationTree_BRIDGE.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_BRIDGE/FanInPrimitive_Req_BRIDGE.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_BRIDGE/FanInPrimitive_Resp_BRIDGE.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_BRIDGE/MUX2_REQ_BRIDGE.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_BRIDGE/RequestBlock1CH_BRIDGE.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_BRIDGE/RequestBlock2CH_BRIDGE.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_BRIDGE/ResponseBlock_BRIDGE.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_BRIDGE/ResponseTree_BRIDGE.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_BRIDGE/RR_Flag_Req_BRIDGE.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/L2_tcdm_hybrid_interco/RTL/XBAR_BRIDGE/XBAR_BRIDGE.sv
