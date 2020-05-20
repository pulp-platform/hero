puts "${Green}Analyzing udma_external_per ${NC}"

puts "${Green}--> compile udma_external_per${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_external_per/rtl/udma_external_per_reg_if.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_external_per/rtl/udma_external_per_wrapper.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_external_per/rtl/udma_external_per_top.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_external_per/rtl/udma_traffic_gen_rx.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_external_per/rtl/udma_traffic_gen_tx.sv
