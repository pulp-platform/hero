vsim axi_dma_tb -t 1ps -voptargs=+acc

set StdArithNoWarnings 1
set NumericStdNoWarnings 1
log -r /*

delete wave *
