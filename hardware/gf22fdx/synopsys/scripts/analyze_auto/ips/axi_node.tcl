puts "${Green}Analyzing axi_node ${NC}"

puts "${Green}--> compile axi_node${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/apb_regs_top.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_address_decoder_AR.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_address_decoder_AW.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_address_decoder_BR.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_address_decoder_BW.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_address_decoder_DW.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_AR_allocator.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_AW_allocator.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_BR_allocator.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_BW_allocator.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_DW_allocator.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_multiplexer.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_node_arbiter.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_node_intf_wrap.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_node.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_node_wrap_with_slices.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_regs_top.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_request_block.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/axi_node/src/axi_response_block.sv
