# Architecture Specification of AXI DMA

This AXI DMA is split into two groups of modules, shown below, to combine reusability with a generic programming interface.  The modules on the right-hand side (green box) provide the basics of moving data over an AXI bus.  The modules on the left-hand side (yellow box) implement the programming interface and can be customized or replaced depdending on the needs of a project.

![](doc/architecture.png)

## Top-Level Parameters

This DMA shall support an AXI address width of 32 and 64 bits, data widths of 8, 16, 32, 64, 128, 256, 512, and 1024 bits, and any ID and user signal width.

## Data Mover

`axi_dma_mover` transfers data over AXI by reading with the `AR` and `R` channels and writing with the `AW`, `W`, and `B` channels.  It takes AXI-compliant `AR` and `AW` beats as input and simply issues them through its master interface.  It realigns the data beats it receives on the `R` channel to beats it sends on the `W` channel.  To occupy the downstream `W` channel for as short as possible, it only sends the `AW` when it is ready to send the first `W` beat.

To minimize internal buffers and since write bursts cannot be reordered, all read bursts have the same ID (so they cannot be reordered either).

### Error Handling

When the Data Mover receives an error response (`RRESP != 0`) on the first read beat, it does not issue the corresponding write.  When it receives an error on a read beat that is not the first, it disables the corresponding byte strobes in the write.  On any first error in a read burst, it signals the `ARADDR` of the burst for which the error occurred at a DMA-internal error interface.

When the Data Mover receives an error response (`BRESP != 0`) on a write, it signals the `AWADDR` of the burst for which the error occurred at a DMA-internal error interface.

## Ax Generator

`axi_dma_ax_gen` converts arbitrary one-dimensional contiguous transfer descriptors (essentially defining the number of bytes to be transferred from a source to a destination address) into a series of AXI-compliant `AR`s and `AW`s.  In particular, there must be one `AW` for every `AR`, and both read and write bursts must respect the rules given in Section A3.4 of the AXI(5) specification.

### Error Handling

When the Ax Generator cannot decompose the transfer descriptor (e.g., because one address plus the number of bytes exceeds the addressable memory), it shall report the error at a DMA-internal error interface and *not* forward any `AR` or `AW` for that descriptor.

## Transfer Flattener

`axi_dma_flattener` generates one-dimensional contiguous transfer descriptors from input descriptors that have a parametrizable dimension, may be strided, and may have unequal strides for source and destination.

For example, an input 3D scatter-gather descriptor with the following parameters

![](doc/multi_dim_scatter_gather.png)

could be
```
{
    src_addr: 0x4000, // byte-wise source base address
    dst_addr: 0xB100, // byte-wise destination base address
    a_cnt:         4, // number of bytes in the inner-most dimension
    a_off_src:   0x5, // offset (in bytes) at source from the end of one 1st-dim block to the next
    a_off_dst:   0x0, // offset (in bytes) at destination from the end of one 1st-dim block to the next
    b_cnt:         3, // number of blocks in the second dimension
    b_off_src:  0x10, // offset (in bytes) at source from the end of one 2nd-dim block to the next
    b_off_dst:   0x0, // offset (in bytes) at destination from the end of one 2nd-dim block to the next
    c_cnt:         3, // number of blocks in the third dimension
}
```
The Transfer Flattener would generate the following descriptors from this (in `{src, dst, size}` format with comments denoting block indices `[outer, inner]`):
```
[
    {0x4000, 0xB100, 4}, // [0, 0]
    {0x4009, 0xB104, 4}, // [0, 1]
    {0x4012, 0xB108, 4}, // [0, 2]
    {0x4026, 0xB10C, 4}, // [1, 0]
    {0x402F, 0xB110, 4}, // [1, 1]
    {0x4038, 0xB114, 4}, // [1, 2]
    {0x404C, 0xB118, 4}, // [2, 0]
    {0x4055, 0xB11C, 4}, // [2, 1]
    {0x405E, 0xB120, 4}, // [2, 2]
]
```