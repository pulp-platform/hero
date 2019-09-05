// Copyright 2019 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

// Configuration package for PULP cluster OOC stub
package automatic pulp_cluster_cfg_pkg;
  // -- Decoupling of cluster clock domain
  localparam bit          ASYNC = 1'b0;
  localparam int unsigned DC_BUF_W = 8;
  // -- Cores
  localparam int unsigned N_CORES = 8; // must be a power of 2 and <= 8
  // -- AXI
  localparam int unsigned AXI_AW = 64; // [bit]
  localparam int unsigned AXI_DW = 64; // [bit]
  localparam int unsigned AXI_IW_MST = 6; // [bit]; do not change, seems to break instruction cache
  localparam int unsigned AXI_IW_SLV = 4; // [bit]
  localparam int unsigned AXI_UW = 4; // [bit]
  // -- DMA
  localparam int unsigned DMA_MAX_BURST_SIZE = 2048; // [B], must be a power of 2
  // Maximum number of beats in a DMA burst on the SoC bus
  localparam int unsigned DMA_MAX_BURST_LEN = DMA_MAX_BURST_SIZE / (AXI_DW/8);
  // Maximum number of transactions the DMA can have in flight
  localparam int unsigned DMA_MAX_N_TXNS = N_CORES;
  localparam int unsigned N_DMAS = 4; // larger values seem to break the cluster
  // -- Instruction Cache
  localparam int unsigned ICACHE_SIZE = 4096; // [B], must be a power of 2
  // -- TCDM
  localparam int unsigned N_TCDM_BANKS = 2*N_CORES; // must be a power of 2
  localparam int unsigned TCDM_SIZE = 256*1024; // [B], must be a power of 2
  // -- L2 Memory (not inside cluster)
  localparam int unsigned L2_SIZE = 256*1024; // [B], must be a power of 2

  typedef logic      [AXI_AW-1:0] addr_t;
  typedef logic             [5:0] cluster_id_t;
  typedef logic      [AXI_DW-1:0] data_t;
  typedef logic    [DC_BUF_W-1:0] dc_buf_t;
  typedef logic  [AXI_IW_MST-1:0] id_mst_t;
  typedef logic  [AXI_IW_SLV-1:0] id_slv_t;
  typedef logic    [AXI_DW/8-1:0] strb_t;
  typedef logic      [AXI_UW-1:0] user_t;
endpackage
