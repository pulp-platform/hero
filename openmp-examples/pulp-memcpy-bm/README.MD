The dma.c file offloads a kernel to the PULP accelerator, which initiates a DMA
transfer to, and a DMA transfer from the L1 memory. The execution times are
measured using performance counters, and printed to stdout.

The dma-noise.c file loops a single DMA transaction, which can be used to
produce memory interference from the PL to the PS.
