// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Wolfgang Rönninger <wroennin@iis.ee.ethz.ch>

`include "typedef.svh"
`include "assign.svh"
/// AXI4+ATOP interface wrapper for `axi_to_mem`
module axi_to_mem_banked_intf #(
  /// AXI4+ATOP ID width
  parameter int unsigned                  AXI_ID_WIDTH   = 32'd0,
  /// AXI4+ATOP address width
  parameter int unsigned                  AXI_ADDR_WIDTH = 32'd0,
  /// AXI4+ATOP data width
  parameter int unsigned                  AXI_DATA_WIDTH = 32'd0,
  /// AXI4+ATOP user width
  parameter int unsigned                  AXI_USER_WIDTH = 32'd0,
  /// Number of memory banks / macros
  /// Has to satisfy:
  /// - MemNumBanks >= 2 * AxiDataWidth / MemDataWidth
  /// - MemNumBanks is a power of 2.
  parameter int unsigned                  MEM_NUM_BANKS  = 32'd4,
  /// Address width of an individual memory bank.
  parameter int unsigned                  MEM_ADDR_WIDTH = 32'd11,
  /// Data width of the memory macros.
  /// Has to satisfy:
  /// - AxiDataWidth % MemDataWidth = 0
  parameter int unsigned                  MEM_DATA_WIDTH = 32'd32,
  /// Read latency of the connected memory in cycles
  parameter int unsigned                  MEM_LATENCY    = 32'd1,
  /// TCDM topology can be: LIC, BFLY2, BFLY4, CLOS
  parameter tcdm_interconnect_pkg::topo_e TOPOLOGY       = tcdm_interconnect_pkg::LIC,
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter type mem_addr_t = logic [MEM_ADDR_WIDTH-1:0],
  parameter type mem_atop_t = logic [5:0],
  parameter type mem_data_t = logic [MEM_DATA_WIDTH-1:0],
  parameter type mem_strb_t = logic [MEM_DATA_WIDTH/8-1:0]
) (
  /// Clock
  input  logic                          clk_i,
  /// Asynchronous reset, active low
  input  logic                          rst_ni,
  /// Testmode enable
  input  logic                          test_i,
  /// AXI4+ATOP slave port
  AXI_BUS.Slave                         slv,
  /// Memory bank request
  output logic      [MEM_NUM_BANKS-1:0] mem_req_o,
  /// Memory request grant
  input  logic      [MEM_NUM_BANKS-1:0] mem_gnt_i,
  /// Request address
  output mem_addr_t [MEM_NUM_BANKS-1:0] mem_add_o,
  /// Write request enable, active high
  output logic      [MEM_NUM_BANKS-1:0] mem_wen_o,
  /// Write data
  output mem_data_t [MEM_NUM_BANKS-1:0] mem_wdata_o,
  /// Write data byte enable, active high
  output mem_strb_t [MEM_NUM_BANKS-1:0] mem_be_o,
  /// Atomic operation
  output mem_atop_t [MEM_NUM_BANKS-1:0] mem_atop_o,
  /// Read data response
  input  mem_data_t [MEM_NUM_BANKS-1:0] mem_rdata_i,
  /// Status output, busy flag of `axi_to_mem`
  output logic      [1:0]               axi_to_mem_busy_o
);
  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(atm_aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(atm_w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(atm_b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(atm_ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(atm_r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, atm_aw_chan_t, atm_w_chan_t, atm_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, atm_b_chan_t, atm_r_chan_t)

  axi_req_t  mem_axi_req;
  axi_resp_t mem_axi_resp;

  `AXI_ASSIGN_TO_REQ(mem_axi_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, mem_axi_resp)

  axi_to_mem_banked #(
    .AxiIdWidth    ( AXI_ID_WIDTH               ),
    .AxiAddrWidth  ( AXI_ADDR_WIDTH             ),
    .AxiDataWidth  ( AXI_DATA_WIDTH             ),
    .axi_aw_chan_t ( atm_aw_chan_t              ),
    .axi_w_chan_t  (  atm_w_chan_t              ),
    .axi_b_chan_t  (  atm_b_chan_t              ),
    .axi_ar_chan_t ( atm_ar_chan_t              ),
    .axi_r_chan_t  (  atm_r_chan_t              ),
    .axi_req_t     ( axi_req_t                  ),
    .axi_resp_t    ( axi_resp_t                 ),
    .MemNumBanks   ( MEM_NUM_BANKS              ),
    .MemAddrWidth  ( MEM_ADDR_WIDTH             ),
    .MemDataWidth  ( MEM_DATA_WIDTH             ),
    .MemLatency    ( MEM_LATENCY                ),
    .Topology      ( tcdm_interconnect_pkg::LIC )
  ) i_axi_to_mem_banked (
    .clk_i,
    .rst_ni,
    .test_i,
    .axi_to_mem_busy_o,
    .axi_req_i      ( mem_axi_req  ),
    .axi_resp_o     ( mem_axi_resp ),
    .mem_req_o,
    .mem_gnt_i,
    .mem_add_o,
    .mem_wdata_o,
    .mem_be_o,
    .mem_atop_o,
    .mem_wen_o,
    .mem_rdata_i
  );

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AXI_ADDR_WIDTH  >= 1) else $fatal(1, "AXI address width must be at least 1!");
    assert (AXI_DATA_WIDTH  >= 1) else $fatal(1, "AXI data width must be at least 1!");
    assert (AXI_ID_WIDTH    >= 1) else $fatal(1, "AXI ID   width must be at least 1!");
    assert (AXI_USER_WIDTH  >= 1) else $fatal(1, "AXI user width must be at least 1!");
  end
`endif
// pragma translate_on
endmodule
