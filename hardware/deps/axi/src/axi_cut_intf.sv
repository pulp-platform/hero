// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Andreas Kurth  <akurth@iis.ee.ethz.ch>

`include "assign.svh"
`include "typedef.svh"

// Interface variant of `axi_cut`.
module axi_cut_intf #(
  // Bypass eneable
  parameter bit          BYPASS     = 1'b0,
  // The address width.
  parameter int unsigned ADDR_WIDTH = 0,
  // The data width.
  parameter int unsigned DATA_WIDTH = 0,
  // The ID width.
  parameter int unsigned ID_WIDTH   = 0,
  // The user data width.
  parameter int unsigned USER_WIDTH = 0
) (
  input logic     clk_i  ,
  input logic     rst_ni ,
  AXI_BUS.Slave   in     ,
  AXI_BUS.Master  out
);

  typedef logic [ID_WIDTH-1:0]     id_t;
  typedef logic [ADDR_WIDTH-1:0]   addr_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;
  typedef logic [USER_WIDTH-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(cut_aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(cut_w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(cut_b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(cut_ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(cut_r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(cut_req_t, cut_aw_chan_t, cut_w_chan_t, cut_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(cut_resp_t, cut_b_chan_t, cut_r_chan_t)

  cut_req_t  slv_req,  mst_req;
  cut_resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, in)
  `AXI_ASSIGN_FROM_RESP(in, slv_resp)

  `AXI_ASSIGN_FROM_REQ(out, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, out)

  axi_cut #(
    .Bypass    ( BYPASS        ),
    .aw_chan_t ( cut_aw_chan_t ),
    .w_chan_t  (  cut_w_chan_t ),
    .b_chan_t  (  cut_b_chan_t ),
    .ar_chan_t ( cut_ar_chan_t ),
    .r_chan_t  (  cut_r_chan_t ),
    .req_t     (     cut_req_t ),
    .resp_t    (    cut_resp_t )
  ) i_axi_cut (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );

  // Check the invariants.
  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assert (ADDR_WIDTH > 0) else $fatal(1, "Wrong addr width parameter");
    assert (DATA_WIDTH > 0) else $fatal(1, "Wrong data width parameter");
    assert (ID_WIDTH   > 0) else $fatal(1, "Wrong id   width parameter");
    assert (USER_WIDTH > 0) else $fatal(1, "Wrong user width parameter");
    assert (in.AXI_ADDR_WIDTH  == ADDR_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (in.AXI_DATA_WIDTH  == DATA_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (in.AXI_ID_WIDTH    == ID_WIDTH)   else $fatal(1, "Wrong interface definition");
    assert (in.AXI_USER_WIDTH  == USER_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_ADDR_WIDTH == ADDR_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_DATA_WIDTH == DATA_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_ID_WIDTH   == ID_WIDTH)   else $fatal(1, "Wrong interface definition");
    assert (out.AXI_USER_WIDTH == USER_WIDTH) else $fatal(1, "Wrong interface definition");
  end
  `endif
  // pragma translate_on
endmodule
