puts "${Green}Analyzing cluster_interconnect ${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/interfaces/tcdm_bank_mem_bus.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/interfaces/xbar_demux_bus.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/interfaces/xbar_periph_bus.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/interfaces/xbar_tcdm_bus_64.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/interfaces/xbar_tcdm_bus.sv

puts "${Green}--> compile low_latency_interco${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/FanInPrimitive_Req.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/ArbitrationTree.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/MUX2_REQ.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/AddressDecoder_Resp.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/TestAndSet.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/RequestBlock2CH.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/RequestBlock1CH.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/FanInPrimitive_Resp.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/ResponseTree.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/ResponseBlock.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/AddressDecoder_Req.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/XBAR_TCDM.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/XBAR_TCDM_WRAPPER.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/TCDM_PIPE_REQ.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/TCDM_PIPE_RESP.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/grant_mask.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/low_latency_interco/priority_Flag_Req.sv

puts "${Green}--> compile peripheral_interco${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/peripheral_interco/AddressDecoder_PE_Req.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/peripheral_interco/AddressDecoder_Resp_PE.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/peripheral_interco/ArbitrationTree_PE.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/peripheral_interco/FanInPrimitive_Req_PE.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/peripheral_interco/RR_Flag_Req_PE.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/peripheral_interco/MUX2_REQ_PE.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/peripheral_interco/FanInPrimitive_PE_Resp.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/peripheral_interco/RequestBlock1CH_PE.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/peripheral_interco/RequestBlock2CH_PE.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/peripheral_interco/ResponseBlock_PE.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/peripheral_interco/ResponseTree_PE.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/peripheral_interco/XBAR_PE.sv

puts "${Green}--> compile tcdm_interconnect${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/tcdm_interconnect/tcdm_interconnect_pkg.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/tcdm_interconnect/addr_dec_resp_mux.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/tcdm_interconnect/amo_shim.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/tcdm_interconnect/xbar.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/tcdm_interconnect/clos_net.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/tcdm_interconnect/bfly_net.sv
analyze -format sverilog  -work work ${IPS_PATH}/cluster_interconnect/rtl/tcdm_interconnect/tcdm_interconnect.sv
