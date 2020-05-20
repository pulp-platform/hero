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

module axi_lite_cut_intf #(
  // bypass enable
  parameter bit          BYPASS     = 1'b0,
  /// The address width.
  parameter int unsigned ADDR_WIDTH = 0,
  /// The data width.
  parameter int unsigned DATA_WIDTH = 0
) (
  input logic     clk_i  ,
  input logic     rst_ni ,
  AXI_LITE.Slave  in     ,
  AXI_LITE.Master out
);

  typedef logic [ADDR_WIDTH-1:0]   addr_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t   slv_req,  mst_req;
  resp_t  slv_resp, mst_resp;

  `AXI_LITE_ASSIGN_TO_REQ(slv_req, in)
  `AXI_LITE_ASSIGN_FROM_RESP(in, slv_resp)

  `AXI_LITE_ASSIGN_FROM_REQ(out, mst_req)
  `AXI_LITE_ASSIGN_TO_RESP(mst_resp, out)

  axi_cut #(
    .Bypass    (    BYPASS ),
    .aw_chan_t ( aw_chan_t ),
    .w_chan_t  (  w_chan_t ),
    .b_chan_t  (  b_chan_t ),
    .ar_chan_t ( ar_chan_t ),
    .r_chan_t  (  r_chan_t ),
    .req_t     (     req_t ),
    .resp_t    (    resp_t )
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
    assert (in.AXI_ADDR_WIDTH == ADDR_WIDTH)  else $fatal(1, "Wrong interface definition");
    assert (in.AXI_DATA_WIDTH == DATA_WIDTH)  else $fatal(1, "Wrong interface definition");
    assert (out.AXI_ADDR_WIDTH == ADDR_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_DATA_WIDTH == DATA_WIDTH) else $fatal(1, "Wrong interface definition");
  end
  `endif
  // pragma translate_on
endmodule
