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

// Author: Robert Balas (balasr@iis.ee.ethz.ch)

module axi_tcdm_if #(
    parameter int unsigned AXI_ADDR_WIDTH = 0,
    parameter int unsigned AXI_DATA_WIDTH = 0,
    parameter int unsigned AXI_USER_WIDTH = 0,
    parameter int unsigned AXI_ID_WIDTH = 0
) (
   input logic                         clk_i,
   input logic                         rst_ni,
   // axi in
   AXI_BUS.Slave                       slave,

   // tcdm out
   output logic                        tcdm_master_req_o,
   output logic [AXI_ADDR_WIDTH-1:0]   tcdm_master_addr_o,
   output logic                        tcdm_master_we_o, // TODO: wen vs we
   output logic [AXI_ADDR_WIDTH/8-1:0] tcdm_master_be_o,
   output logic [AXI_DATA_WIDTH-1:0]   tcdm_master_data_o,
   input logic                         tcdm_master_gnt_i, // TODO: ignored

   input logic                         tcdm_master_r_valid_i, // TODO: ignored
   input logic [AXI_DATA_WIDTH-1:0]    tcdm_master_r_data_i
);

  axi_mem_if #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH)
  ) i_axi_mem_if (
    .clk_i,
    .rst_ni,
    .slave  (slave),
    .req_o  (tcdm_master_req_o),
    .we_o   (tcdm_master_we_o),
    .addr_o (tcdm_master_addr_o),
    .be_o   (tcdm_master_be_o),
    .data_o (tcdm_master_data_o),

    .data_i (tcdm_master_r_data_i)
  );

  // TODO: extend this to full tcdm protocol. For that we have to consider
  // tcdm_master_r_valid_i and tcdm_master_gnt_i. This probably means we have to
  // fork and adapt axi_mem_if. Currently axi_mem_if is compatible with tcdm if
  // we "react" in one cycle.

  // For now we just put in some assertions that signal protocol violations
`ifndef VERILATOR
  assert property (@(posedge clk_i)
    disable iff (!rst_ni)
    tcdm_master_req_o == tcdm_master_gnt_i); // immediately allow changing addr

  assert property (@(posedge clk_i)
    disable iff (!rst_ni)
    tcdm_master_gnt_i |=> tcdm_master_r_valid_i); // generic: after grant need response next cycle

`endif
endmodule // axi_tcdm_if
