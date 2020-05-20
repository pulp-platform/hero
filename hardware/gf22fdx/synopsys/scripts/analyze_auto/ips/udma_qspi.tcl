puts "${Green}Analyzing udma_qspi ${NC}"

puts "${Green}--> compile udma_qspi${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_qspi/rtl/udma_spim_reg_if.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_qspi/rtl/udma_spim_ctrl.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_qspi/rtl/udma_spim_txrx.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_qspi/rtl/udma_spim_top.sv
