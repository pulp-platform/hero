// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Andreas Kurth <akurth@iis.ee.ethz.ch>


`include "assign.svh"
`include "typedef.svh"
// Interface wrapper for axi_to_mem
module axi_to_mem_intf #(
  parameter int unsigned AddrWidth = 0,
  parameter int unsigned DataWidth = 0,
  parameter int unsigned IdWidth = 0,
  parameter int unsigned UserWidth = 0,
  parameter int unsigned NumBanks = 0,
  parameter int unsigned BufDepth = 1,  // depth of memory response buffer
  // Dependent parameters, do not override.
  parameter type addr_t = logic [AddrWidth-1:0],
  parameter type mem_atop_t = logic [5:0],
  parameter type mem_data_t = logic [DataWidth/NumBanks-1:0],
  parameter type mem_strb_t = logic [DataWidth/NumBanks/8-1:0]
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  output logic                      busy_o,

  AXI_BUS.Slave                     slv,

  output logic      [NumBanks-1:0]  mem_req_o,
  input  logic      [NumBanks-1:0]  mem_gnt_i,
  output addr_t     [NumBanks-1:0]  mem_addr_o,   // byte address
  output mem_data_t [NumBanks-1:0]  mem_wdata_o,  // write data
  output mem_strb_t [NumBanks-1:0]  mem_strb_o,   // byte-wise strobe
  output mem_atop_t [NumBanks-1:0]  mem_atop_o,   // atomic operation
  output logic      [NumBanks-1:0]  mem_we_o,     // write enable
  input  logic      [NumBanks-1:0]  mem_rvalid_i, // response valid
  input  mem_data_t [NumBanks-1:0]  mem_rdata_i   // read data
);
  typedef logic [IdWidth-1:0]     id_t;
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  typedef logic [UserWidth-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)
  req_t   req;
  resp_t  resp;
  `AXI_ASSIGN_TO_REQ(req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, resp)
  axi_to_mem #(
    .axi_req_t  (req_t),
    .axi_resp_t (resp_t),
    .AddrWidth  (AddrWidth),
    .DataWidth  (DataWidth),
    .IdWidth    (IdWidth),
    .NumBanks   (NumBanks),
    .BufDepth   (BufDepth)
  ) i_axi_to_mem (
    .clk_i,
    .rst_ni,
    .busy_o,
    .axi_req_i  (req),
    .axi_resp_o (resp),
    .mem_req_o,
    .mem_gnt_i,
    .mem_addr_o,
    .mem_wdata_o,
    .mem_strb_o,
    .mem_atop_o,
    .mem_we_o,
    .mem_rvalid_i,
    .mem_rdata_i
  );
endmodule
