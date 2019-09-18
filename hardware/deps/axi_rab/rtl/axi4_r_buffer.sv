// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module axi4_r_buffer
  #(
    parameter AXI_DATA_WIDTH = 32,
    parameter AXI_ID_WIDTH   = 4,
    parameter AXI_USER_WIDTH = 4
  )
  (
    input  logic                      axi4_aclk,
    input  logic                      axi4_arstn,

    output logic   [AXI_ID_WIDTH-1:0] s_axi4_rid,
    output logic                [1:0] s_axi4_rresp,
    output logic [AXI_DATA_WIDTH-1:0] s_axi4_rdata,
    output logic                      s_axi4_rlast,
    output logic                      s_axi4_rvalid,
    output logic [AXI_USER_WIDTH-1:0] s_axi4_ruser,
    input  logic                      s_axi4_rready,

    input  logic   [AXI_ID_WIDTH-1:0] m_axi4_rid,
    input  logic                [1:0] m_axi4_rresp,
    input  logic [AXI_DATA_WIDTH-1:0] m_axi4_rdata,
    input  logic                      m_axi4_rlast,
    input  logic                      m_axi4_rvalid,
    input  logic [AXI_USER_WIDTH-1:0] m_axi4_ruser,
    output logic                      m_axi4_rready
  );

  wire [AXI_DATA_WIDTH+AXI_ID_WIDTH+AXI_USER_WIDTH+3-1:0] data_in;
  wire [AXI_DATA_WIDTH+AXI_ID_WIDTH+AXI_USER_WIDTH+3-1:0] data_out;

  localparam ID_START   = 3;
  localparam ID_END     = AXI_ID_WIDTH-1 + ID_START;
  localparam DATA_START = ID_END + 1;
  localparam DATA_END   = AXI_DATA_WIDTH-1 + DATA_START;
  localparam USER_START = DATA_END + 1;
  localparam USER_END   = AXI_USER_WIDTH-1 + USER_START;

  assign data_in                [1:0] = m_axi4_rresp;
  assign data_in                  [2] = m_axi4_rlast;
  assign data_in    [ID_END:ID_START] = m_axi4_rid;
  assign data_in[DATA_END:DATA_START] = m_axi4_rdata;
  assign data_in[USER_END:USER_START] = m_axi4_ruser;

  assign s_axi4_rresp  = data_out                [1:0];
  assign s_axi4_rlast  = data_out                  [2];
  assign s_axi4_rid    = data_out    [ID_END:ID_START];
  assign s_axi4_rdata  = data_out[DATA_END:DATA_START];
  assign s_axi4_ruser  = data_out[USER_END:USER_START];

  axi_buffer_rab
  #(
    .DATA_WIDTH   ( AXI_DATA_WIDTH+AXI_ID_WIDTH+AXI_USER_WIDTH+3  ),
    .BUFFER_DEPTH ( 4                                             )
    )
  u_buffer
  (
    .clk       ( axi4_aclk     ),
    .rstn      ( axi4_arstn    ),
    // Pop
    .valid_out ( s_axi4_rvalid ),
    .data_out  ( data_out      ),
    .ready_in  ( s_axi4_rready ),
    // Push
    .valid_in  ( m_axi4_rvalid ),
    .data_in   ( data_in       ),
    .ready_out ( m_axi4_rready )
  );

endmodule
