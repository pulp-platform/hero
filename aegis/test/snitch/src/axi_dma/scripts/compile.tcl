vlib work

vlog  -work work -sv src/axi_dma_pkg.sv
vlog  -work work -sv src/axi_dma_data_path.sv
vlog  -work work -sv src/axi_dma_data_mover.sv
vlog  -work work -sv src/axi_dma_burst_reshaper.sv
vlog  -work work -sv src/axi_dma_backend.sv
vlog  -work work -sv src/axi_dma_error_handler.sv
vlog  -work work -sv src/axi_dma_perf_counters.sv
vlog  -work work -sv src/axi_dma_twod_ext.sv
vlog  -work work -sv ../common_cells/src/fifo_v3.sv
vlog  -work work -sv ../common_cells/src/popcount.sv

vlog  -work work -sv test/fixture_oned_axi_dma.sv
vlog  -work work -sv test/axi_dma_tb.sv
