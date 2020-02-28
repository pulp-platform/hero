puts "${Green}Analyzing udma_filter ${NC}"

puts "${Green}--> compile udma_filter${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_filter/rtl/udma_filter_au.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_filter/rtl/udma_filter_bincu.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_filter/rtl/udma_filter_rx_dataout.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_filter/rtl/udma_filter_tx_datafetch.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_filter/rtl/udma_filter_reg_if.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_filter/rtl/udma_filter.sv
