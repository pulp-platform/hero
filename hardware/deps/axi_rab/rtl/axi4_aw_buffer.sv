// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module axi4_aw_buffer
  #(
    parameter AXI_ID_WIDTH   = 4,
    parameter AXI_USER_WIDTH = 4
  )
  (
    input  logic                      axi4_aclk,
    input  logic                      axi4_arstn,

    input  logic   [AXI_ID_WIDTH-1:0] s_axi4_awid,
    input  logic               [31:0] s_axi4_awaddr,
    input  logic                      s_axi4_awvalid,
    output logic                      s_axi4_awready,
    input  logic                [7:0] s_axi4_awlen,
    input  logic                [2:0] s_axi4_awsize,
    input  logic                [1:0] s_axi4_awburst,
    input  logic                      s_axi4_awlock,
    input  logic                [2:0] s_axi4_awprot,
    input  logic                [3:0] s_axi4_awcache,
    input  logic                [3:0] s_axi4_awregion,
    input  logic                [3:0] s_axi4_awqos,
    input  logic [AXI_USER_WIDTH-1:0] s_axi4_awuser,

    output logic   [AXI_ID_WIDTH-1:0] m_axi4_awid,
    output logic               [31:0] m_axi4_awaddr,
    output logic                      m_axi4_awvalid,
    input  logic                      m_axi4_awready,
    output logic                [7:0] m_axi4_awlen,
    output logic                [2:0] m_axi4_awsize,
    output logic                [1:0] m_axi4_awburst,
    output logic                      m_axi4_awlock,
    output logic                [2:0] m_axi4_awprot,
    output logic                [3:0] m_axi4_awcache,
    output logic                [3:0] m_axi4_awregion,
    output logic                [3:0] m_axi4_awqos,
    output logic [AXI_USER_WIDTH-1:0] m_axi4_awuser
  );

  wire [AXI_USER_WIDTH+AXI_ID_WIDTH+60:0] data_in;
  wire [AXI_USER_WIDTH+AXI_ID_WIDTH+60:0] data_out;

  assign data_in                                            [3:0] = s_axi4_awcache;
  assign data_in                                            [6:4] = s_axi4_awprot;
  assign data_in                                              [7] = s_axi4_awlock;
  assign data_in                                            [9:8] = s_axi4_awburst;
  assign data_in                                          [12:10] = s_axi4_awsize;
  assign data_in                                          [20:13] = s_axi4_awlen;
  assign data_in                                          [52:21] = s_axi4_awaddr;
  assign data_in                                          [56:53] = s_axi4_awregion;
  assign data_in                                          [60:57] = s_axi4_awqos;
  assign data_in                             [60+AXI_ID_WIDTH:61] = s_axi4_awid;
  assign data_in [60+AXI_ID_WIDTH+AXI_USER_WIDTH:61+AXI_ID_WIDTH] = s_axi4_awuser;

  assign m_axi4_awcache  = data_out[3:0];
  assign m_axi4_awprot   = data_out[6:4];
  assign m_axi4_awlock   = data_out[7];
  assign m_axi4_awburst  = data_out[9:8];
  assign m_axi4_awsize   = data_out[12:10];
  assign m_axi4_awlen    = data_out[20:13];
  assign m_axi4_awaddr   = data_out[52:21];
  assign m_axi4_awregion = data_out[56:53];
  assign m_axi4_awqos    = data_out[60:57];
  assign m_axi4_awid     = data_out[60+AXI_ID_WIDTH:61];
  assign m_axi4_awuser   = data_out[60+AXI_ID_WIDTH+AXI_USER_WIDTH:61+AXI_ID_WIDTH];

  axi_buffer_rab
    #(
      .DATA_WIDTH   ( AXI_ID_WIDTH+AXI_USER_WIDTH+61  ),
      .BUFFER_DEPTH ( 4                               )
    )
    u_buffer
    (
      .clk       ( axi4_aclk      ),
      .rstn      ( axi4_arstn     ),
      .valid_out ( m_axi4_awvalid ),
      .data_out  ( data_out       ),
      .ready_in  ( m_axi4_awready ),
      .valid_in  ( s_axi4_awvalid ),
      .data_in   ( data_in        ),
      .ready_out ( s_axi4_awready )
    );
endmodule
