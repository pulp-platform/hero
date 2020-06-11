// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Configuration package for PULP cluster OOC stub
package pulp_cluster_cfg_pkg;
  // -- Decoupling of cluster clock domain
  localparam bit          ASYNC = 1'b0;
  localparam int unsigned DC_BUF_W = 8;
  // -- Cores
  localparam int unsigned N_CORES = 8; // must be a power of 2 and <= 8
  localparam logic [31:0] ROM_BOOT_ADDR = 32'h1A00_0000;
  localparam logic [31:0] BOOT_ADDR = 32'h1C00_0080;
  // -- SoC peripherals
  localparam logic [31:0] SOC_PERIPH_BASE_ADDR = 32'h1D10_0000; // begin of address space
  localparam int unsigned SOC_PERIPH_SIZE = 32 * 1024; // 32kB
  // -- Debug module
  localparam logic [31:0] DM_BASE_ADDR = 32'h1D00_0000; // begin of address space
  localparam int unsigned DM_SIZE = 16 * 1024; // 16kB according to debug-system.md
  localparam logic [31:0] DM_ROM_ADDR = DM_BASE_ADDR + 32'h800;
  // -- AXI
  localparam int unsigned AXI_AW = 32; // [bit]
  localparam int unsigned AXI_DW = 64; // [bit]
  localparam int unsigned AXI_IW_MST = 5; // [bit]; do not change, seems to break instruction cache
  localparam int unsigned AXI_IW_SLV = 3; // [bit]
  localparam int unsigned AXI_UW = 4; // [bit]
  // -- DMA
  localparam int unsigned DMA_MAX_BURST_SIZE = 128; // [B], must be a power of 2
  // Maximum number of beats in a DMA burst on the SoC bus
  localparam int unsigned DMA_MAX_BURST_LEN = DMA_MAX_BURST_SIZE / (AXI_DW/8);
  // Maximum number of transactions the DMA can have in flight
  localparam int unsigned DMA_MAX_N_TXNS = 16;
  localparam int unsigned N_DMAS = 4; // larger values seem to break the cluster
  // -- Instruction Cache
  localparam int unsigned ICACHE_SIZE = 4096; // [B], must be a power of 2
  // -- TCDM
  localparam int unsigned N_TCDM_BANKS = 2*N_CORES; // must be a power of 2
  localparam int unsigned TCDM_SIZE = 128*1024; // [B], must be a power of 2
  // -- L2 Memory (not inside cluster)
  localparam int unsigned L2_SIZE = 128*1024; // [B], must be a power of 2

  typedef logic      [AXI_AW-1:0] addr_t;
  typedef logic             [5:0] cluster_id_t;
  typedef logic      [AXI_DW-1:0] data_t;
  typedef logic    [DC_BUF_W-1:0] dc_buf_t;
  typedef logic  [AXI_IW_MST-1:0] id_mst_t;
  typedef logic  [AXI_IW_SLV-1:0] id_slv_t;
  typedef logic    [AXI_DW/8-1:0] strb_t;
  typedef logic      [AXI_UW-1:0] user_t;
endpackage
