// Copyright (c) 2014-2019 ETH Zurich, University of Bologna
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
// Andreas Kurth <akurth@iis.ee.ethz.ch>
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// axi_id_resize with flat port list (e.g., for use in Verilog files)
module axi_id_resize_ports #(
  parameter int unsigned ADDR_WIDTH   = 0,
  parameter int unsigned DATA_WIDTH   = 0,
  parameter int unsigned USER_WIDTH   = 0,
  parameter int unsigned ID_WIDTH_IN  = 0,
  parameter int unsigned ID_WIDTH_OUT = 0,
  parameter int unsigned TABLE_SIZE   = 0,
  parameter type addr_t = logic [ADDR_WIDTH-1:0],
  parameter type data_t = logic [DATA_WIDTH-1:0],
  parameter type id_in_t = logic [ID_WIDTH_IN-1:0],
  parameter type id_out_t = logic [ID_WIDTH_OUT-1:0],
  parameter type strb_t = logic [DATA_WIDTH/8-1:0],
  parameter type user_t = logic [USER_WIDTH-1:0]
) (
  input logic     clk_i,
  input logic     rst_ni,

  input  id_in_t            in_aw_id_i,
  input  addr_t             in_aw_addr_i,
  input  axi_pkg::len_t     in_aw_len_i,
  input  axi_pkg::size_t    in_aw_size_i,
  input  axi_pkg::burst_t   in_aw_burst_i,
  input  logic              in_aw_lock_i,
  input  axi_pkg::cache_t   in_aw_cache_i,
  input  axi_pkg::prot_t    in_aw_prot_i,
  input  axi_pkg::qos_t     in_aw_qos_i,
  input  axi_pkg::region_t  in_aw_region_i,
  input  axi_pkg::atop_t    in_aw_atop_i,
  input  user_t             in_aw_user_i,
  input  logic              in_aw_valid_i,
  output logic              in_aw_ready_o,
  input  data_t             in_w_data_i,
  input  strb_t             in_w_strb_i,
  input  logic              in_w_last_i,
  input  user_t             in_w_user_i,
  input  logic              in_w_valid_i,
  output logic              in_w_ready_o,
  output id_in_t            in_b_id_o,
  output axi_pkg::resp_t    in_b_resp_o,
  output user_t             in_b_user_o,
  output logic              in_b_valid_o,
  input  logic              in_b_ready_i,
  input  id_in_t            in_ar_id_i,
  input  addr_t             in_ar_addr_i,
  input  axi_pkg::len_t     in_ar_len_i,
  input  axi_pkg::size_t    in_ar_size_i,
  input  axi_pkg::burst_t   in_ar_burst_i,
  input  logic              in_ar_lock_i,
  input  axi_pkg::cache_t   in_ar_cache_i,
  input  axi_pkg::prot_t    in_ar_prot_i,
  input  axi_pkg::qos_t     in_ar_qos_i,
  input  axi_pkg::region_t  in_ar_region_i,
  input  user_t             in_ar_user_i,
  input  logic              in_ar_valid_i,
  output logic              in_ar_ready_o,
  output id_in_t            in_r_id_o,
  output data_t             in_r_data_o,
  output axi_pkg::resp_t    in_r_resp_o,
  output logic              in_r_last_o,
  output user_t             in_r_user_o,
  output logic              in_r_valid_o,
  input  logic              in_r_ready_i,

  output id_out_t           out_aw_id_o,
  output addr_t             out_aw_addr_o,
  output axi_pkg::len_t     out_aw_len_o,
  output axi_pkg::size_t    out_aw_size_o,
  output axi_pkg::burst_t   out_aw_burst_o,
  output logic              out_aw_lock_o,
  output axi_pkg::cache_t   out_aw_cache_o,
  output axi_pkg::prot_t    out_aw_prot_o,
  output axi_pkg::qos_t     out_aw_qos_o,
  output axi_pkg::region_t  out_aw_region_o,
  output axi_pkg::atop_t    out_aw_atop_o,
  output user_t             out_aw_user_o,
  output logic              out_aw_valid_o,
  input  logic              out_aw_ready_i,
  output data_t             out_w_data_o,
  output strb_t             out_w_strb_o,
  output logic              out_w_last_o,
  output user_t             out_w_user_o,
  output logic              out_w_valid_o,
  input  logic              out_w_ready_i,
  input  id_out_t           out_b_id_i,
  input  axi_pkg::resp_t    out_b_resp_i,
  input  user_t             out_b_user_i,
  input  logic              out_b_valid_i,
  output logic              out_b_ready_o,
  output id_out_t           out_ar_id_o,
  output addr_t             out_ar_addr_o,
  output axi_pkg::len_t     out_ar_len_o,
  output axi_pkg::size_t    out_ar_size_o,
  output axi_pkg::burst_t   out_ar_burst_o,
  output logic              out_ar_lock_o,
  output axi_pkg::cache_t   out_ar_cache_o,
  output axi_pkg::prot_t    out_ar_prot_o,
  output axi_pkg::qos_t     out_ar_qos_o,
  output axi_pkg::region_t  out_ar_region_o,
  output user_t             out_ar_user_o,
  output logic              out_ar_valid_o,
  input  logic              out_ar_ready_i,
  input  id_out_t           out_r_id_i,
  input  data_t             out_r_data_i,
  input  axi_pkg::resp_t    out_r_resp_i,
  input  logic              out_r_last_i,
  input  user_t             out_r_user_i,
  input  logic              out_r_valid_i,
  output logic              out_r_ready_o
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH (ADDR_WIDTH),
    .AXI_DATA_WIDTH (DATA_WIDTH),
    .AXI_ID_WIDTH   (ID_WIDTH_IN),
    .AXI_USER_WIDTH (USER_WIDTH)
  ) in ();
  assign in.aw_id = in_aw_id_i;
  assign in.aw_addr = in_aw_addr_i;
  assign in.aw_len = in_aw_len_i;
  assign in.aw_size = in_aw_size_i;
  assign in.aw_burst = in_aw_burst_i;
  assign in.aw_lock = in_aw_lock_i;
  assign in.aw_cache = in_aw_cache_i;
  assign in.aw_prot = in_aw_prot_i;
  assign in.aw_qos = in_aw_qos_i;
  assign in.aw_region = in_aw_region_i;
  assign in.aw_atop = in_aw_atop_i;
  assign in.aw_user = in_aw_user_i;
  assign in.aw_valid = in_aw_valid_i;
  assign in_aw_ready_o = in.aw_ready;
  assign in.w_data = in_w_data_i;
  assign in.w_strb = in_w_strb_i;
  assign in.w_last = in_w_last_i;
  assign in.w_user = in_w_user_i;
  assign in.w_valid = in_w_valid_i;
  assign in_w_ready_o = in.w_ready;
  assign in_b_id_o = in.b_id;
  assign in_b_resp_o = in.b_resp;
  assign in_b_user_o = in.b_user;
  assign in_b_valid_o = in.b_valid;
  assign in.b_ready = in_b_ready_i;
  assign in.ar_id = in_ar_id_i;
  assign in.ar_addr = in_ar_addr_i;
  assign in.ar_len = in_ar_len_i;
  assign in.ar_size = in_ar_size_i;
  assign in.ar_burst = in_ar_burst_i;
  assign in.ar_lock = in_ar_lock_i;
  assign in.ar_cache = in_ar_cache_i;
  assign in.ar_prot = in_ar_prot_i;
  assign in.ar_qos = in_ar_qos_i;
  assign in.ar_region = in_ar_region_i;
  assign in.ar_user = in_ar_user_i;
  assign in.ar_valid = in_ar_valid_i;
  assign in_ar_ready_o = in.ar_ready;
  assign in_r_id_o = in.r_id;
  assign in_r_data_o = in.r_data;
  assign in_r_resp_o = in.r_resp;
  assign in_r_last_o = in.r_last;
  assign in_r_user_o = in.r_user;
  assign in_r_valid_o = in.r_valid;
  assign in.r_ready = in_r_ready_i;

  AXI_BUS #(
    .AXI_ADDR_WIDTH (ADDR_WIDTH),
    .AXI_DATA_WIDTH (DATA_WIDTH),
    .AXI_ID_WIDTH   (ID_WIDTH_OUT),
    .AXI_USER_WIDTH (USER_WIDTH)
  ) out ();
  assign out_aw_id_o = out.aw_id;
  assign out_aw_addr_o = out.aw_addr;
  assign out_aw_len_o = out.aw_len;
  assign out_aw_size_o = out.aw_size;
  assign out_aw_burst_o = out.aw_burst;
  assign out_aw_lock_o = out.aw_lock;
  assign out_aw_cache_o = out.aw_cache;
  assign out_aw_prot_o = out.aw_prot;
  assign out_aw_qos_o = out.aw_qos;
  assign out_aw_region_o = out.aw_region;
  assign out_aw_atop_o = out.aw_atop;
  assign out_aw_user_o = out.aw_user;
  assign out_aw_valid_o = out.aw_valid;
  assign out.aw_ready = out_aw_ready_i;
  assign out_w_data_o = out.w_data;
  assign out_w_strb_o = out.w_strb;
  assign out_w_last_o = out.w_last;
  assign out_w_user_o = out.w_user;
  assign out_w_valid_o = out.w_valid;
  assign out.w_ready = out_w_ready_i;
  assign out.b_id = out_b_id_i;
  assign out.b_resp = out_b_resp_i;
  assign out.b_user = out_b_user_i;
  assign out.b_valid = out_b_valid_i;
  assign out_b_ready_o = out.b_ready;
  assign out_ar_id_o = out.ar_id;
  assign out_ar_addr_o = out.ar_addr;
  assign out_ar_len_o = out.ar_len;
  assign out_ar_size_o = out.ar_size;
  assign out_ar_burst_o = out.ar_burst;
  assign out_ar_lock_o = out.ar_lock;
  assign out_ar_cache_o = out.ar_cache;
  assign out_ar_prot_o = out.ar_prot;
  assign out_ar_qos_o = out.ar_qos;
  assign out_ar_region_o = out.ar_region;
  assign out_ar_user_o = out.ar_user;
  assign out_ar_valid_o = out.ar_valid;
  assign out.ar_ready = out_ar_ready_i;
  assign out.r_id = out_r_id_i;
  assign out.r_data = out_r_data_i;
  assign out.r_resp = out_r_resp_i;
  assign out.r_last = out_r_last_i;
  assign out.r_user = out_r_user_i;
  assign out.r_valid = out_r_valid_i;
  assign out_r_ready_o = out.r_ready;

  axi_id_resize #(
    .ADDR_WIDTH   (ADDR_WIDTH),
    .DATA_WIDTH   (DATA_WIDTH),
    .USER_WIDTH   (USER_WIDTH),
    .ID_WIDTH_IN  (ID_WIDTH_IN),
    .ID_WIDTH_OUT (ID_WIDTH_OUT),
    .TABLE_SIZE   (TABLE_SIZE)
  ) i_resize (
    .clk_i,
    .rst_ni,
    .in   (in),
    .out  (out)
  );

endmodule
