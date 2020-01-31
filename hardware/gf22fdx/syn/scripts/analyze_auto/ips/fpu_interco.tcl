puts "${Green}Analyzing fpu_interco ${NC}"

puts "${Green}--> compile fpu_interco${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/../riscv/rtl/include/riscv_defines.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/FP_WRAP/fp_iter_divsqrt_msv_wrapper_2_STAGE.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/FP_WRAP/fpnew_wrapper.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/AddressDecoder_Req_FPU.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/AddressDecoder_Resp_FPU.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/ArbitrationTree_FPU.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/FanInPrimitive_Req_FPU.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/FanInPrimitive_Resp_FPU.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/optimal_alloc.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/FPU_clock_gating.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/LFSR_FPU.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/RequestBlock_FPU.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/ResponseBlock_FPU.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/ResponseTree_FPU.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/RR_Flag_Req_FPU.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/shared_fpu_cluster.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/fpu_demux.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpu_interco/RTL/XBAR_FPU.sv
