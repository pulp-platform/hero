// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module axi4_ar_buffer
  #(
    parameter AXI_ID_WIDTH   = 4,
    parameter AXI_USER_WIDTH = 4
  )
  (
    input  logic                      axi4_aclk,
    input  logic                      axi4_arstn,

    input  logic   [AXI_ID_WIDTH-1:0] s_axi4_arid,
    input  logic               [31:0] s_axi4_araddr,
    input  logic                      s_axi4_arvalid,
    output logic                      s_axi4_arready,
    input  logic                [7:0] s_axi4_arlen,
    input  logic                [2:0] s_axi4_arsize,
    input  logic                [1:0] s_axi4_arburst,
    input  logic                      s_axi4_arlock,
    input  logic                [2:0] s_axi4_arprot,
    input  logic                [3:0] s_axi4_arcache,
    input  logic [AXI_USER_WIDTH-1:0] s_axi4_aruser,

    output logic   [AXI_ID_WIDTH-1:0] m_axi4_arid,
    output logic               [31:0] m_axi4_araddr,
    output logic                      m_axi4_arvalid,
    input  logic                      m_axi4_arready,
    output logic                [7:0] m_axi4_arlen,
    output logic                [2:0] m_axi4_arsize,
    output logic                [1:0] m_axi4_arburst,
    output logic                      m_axi4_arlock,
    output logic                [2:0] m_axi4_arprot,
    output logic                [3:0] m_axi4_arcache,
    output logic [AXI_USER_WIDTH-1:0] m_axi4_aruser
  );

  wire [AXI_ID_WIDTH+AXI_USER_WIDTH+52:0] data_in;
  wire [AXI_ID_WIDTH+AXI_USER_WIDTH+52:0] data_out;

  assign data_in                                           [3:0] = s_axi4_arcache;
  assign data_in                                           [6:4] = s_axi4_arprot;
  assign data_in                                             [7] = s_axi4_arlock;
  assign data_in                                           [9:8] = s_axi4_arburst;
  assign data_in                                         [12:10] = s_axi4_arsize;
  assign data_in                                         [20:13] = s_axi4_arlen;
  assign data_in                                         [52:21] = s_axi4_araddr;
  assign data_in                            [52+AXI_ID_WIDTH:53] = s_axi4_arid;
  assign data_in[52+AXI_ID_WIDTH+AXI_USER_WIDTH:53+AXI_ID_WIDTH] = s_axi4_aruser;

  assign m_axi4_arcache = data_out[3:0];
  assign m_axi4_arprot  = data_out[6:4];
  assign m_axi4_arlock  = data_out[7];
  assign m_axi4_arburst = data_out[9:8];
  assign m_axi4_arsize  = data_out[12:10];
  assign m_axi4_arlen   = data_out[20:13];
  assign m_axi4_araddr  = data_out[52:21];
  assign m_axi4_arid    = data_out[52+AXI_ID_WIDTH:53];
  assign m_axi4_aruser  = data_out[52+AXI_ID_WIDTH+AXI_USER_WIDTH:53+AXI_ID_WIDTH];

  axi_buffer_rab
    #(
      .DATA_WIDTH   ( AXI_ID_WIDTH+AXI_USER_WIDTH+53  ),
      .BUFFER_DEPTH ( 4                               )
      )
    u_buffer
    (
      .clk       ( axi4_aclk      ),
      .rstn      ( axi4_arstn     ),
      .valid_out ( m_axi4_arvalid ),
      .data_out  ( data_out       ),
      .ready_in  ( m_axi4_arready ),
      .valid_in  ( s_axi4_arvalid ),
      .data_in   ( data_in        ),
      .ready_out ( s_axi4_arready )
    );

endmodule


