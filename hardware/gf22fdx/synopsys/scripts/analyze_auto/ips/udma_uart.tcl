puts "${Green}Analyzing udma_uart ${NC}"

puts "${Green}--> compile udma_uart${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_uart/rtl/udma_uart_reg_if.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_uart/rtl/udma_uart_top.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_uart/rtl/udma_uart_rx.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_uart/rtl/udma_uart_tx.sv
