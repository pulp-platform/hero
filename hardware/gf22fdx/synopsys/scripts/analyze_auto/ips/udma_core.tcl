puts "${Green}Analyzing udma_core ${NC}"

puts "${Green}--> compile udma_core${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/core/udma_ch_addrgen.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/core/udma_arbiter.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/core/udma_core.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/core/udma_rx_channels.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/core/udma_tx_channels.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/core/udma_stream_unit.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/common/udma_ctrl.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/common/udma_apb_if.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/common/io_clk_gen.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/common/io_event_counter.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/common/io_generic_fifo.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/common/io_tx_fifo.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/common/io_tx_fifo_mark.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/common/io_tx_fifo_dc.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/common/io_shiftreg.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/common/udma_dc_fifo.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/common/udma_clkgen.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_core/rtl/common/udma_clk_div_cnt.sv
