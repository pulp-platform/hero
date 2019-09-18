// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module axi4_b_buffer
  #(
    parameter AXI_ID_WIDTH   = 4,
    parameter AXI_USER_WIDTH = 4
  )
  (
    input  logic                      axi4_aclk,
    input  logic                      axi4_arstn,

    output logic   [AXI_ID_WIDTH-1:0] s_axi4_bid,
    output logic                [1:0] s_axi4_bresp,
    output logic                      s_axi4_bvalid,
    output logic [AXI_USER_WIDTH-1:0] s_axi4_buser,
    input  logic                      s_axi4_bready,

    input  logic   [AXI_ID_WIDTH-1:0] m_axi4_bid,
    input  logic                [1:0] m_axi4_bresp,
    input  logic                      m_axi4_bvalid,
    input  logic [AXI_USER_WIDTH-1:0] m_axi4_buser,
    output logic                      m_axi4_bready
  );

  wire [AXI_ID_WIDTH+AXI_USER_WIDTH+1:0] data_in;
  wire [AXI_ID_WIDTH+AXI_USER_WIDTH+1:0] data_out;

  assign data_in                                         [1:0] = m_axi4_bresp;
  assign data_in                            [AXI_ID_WIDTH+1:2] = m_axi4_bid;
  assign data_in[AXI_ID_WIDTH+AXI_USER_WIDTH+1:AXI_ID_WIDTH+2] = m_axi4_buser;

  assign s_axi4_buser = data_out[AXI_ID_WIDTH+AXI_USER_WIDTH+1:AXI_ID_WIDTH+2];
  assign s_axi4_bid   = data_out[AXI_ID_WIDTH+1:2];
  assign s_axi4_bresp = data_out[1:0];

  axi_buffer_rab
  #(
    .DATA_WIDTH   ( AXI_ID_WIDTH+AXI_USER_WIDTH+2 ),
    .BUFFER_DEPTH ( 4                             )
    )
  u_buffer
  (
    .clk      ( axi4_aclk     ),
    .rstn     ( axi4_arstn    ),
    .valid_out( s_axi4_bvalid ),
    .data_out ( data_out      ),
    .ready_in ( s_axi4_bready ),
    .valid_in ( m_axi4_bvalid ),
    .data_in  ( data_in       ),
    .ready_out( m_axi4_bready )
  );

endmodule
