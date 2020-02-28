puts "${Green}Analyzing udma_sdio ${NC}"

puts "${Green}--> compile udma_sdio${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_sdio/rtl/sdio_crc7.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_sdio/rtl/sdio_crc16.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_sdio/rtl/sdio_txrx_cmd.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_sdio/rtl/sdio_txrx_data.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_sdio/rtl/sdio_txrx.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_sdio/rtl/udma_sdio_reg_if.sv
analyze -format sverilog  -work work ${IPS_PATH}/udma/udma_sdio/rtl/udma_sdio_top.sv
