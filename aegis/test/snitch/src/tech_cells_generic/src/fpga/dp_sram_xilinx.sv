// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba    <zarubaf@iis.ee.ethz.ch>, ETH Zurich
//         Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: True Dual Ported SRAM
//
module dp_sram #(
    parameter int unsigned DataWidth = 64,
    parameter int unsigned NumWords  = 1024,
    parameter bit          OutRegs   = 0,   // enables output registers in FPGA macro (read lat = 2)
    parameter logic [1:0]  SimInit   = 0    // no-effect here
)(
   input  logic                              clk_i,
   input  logic                              rst_ni,
   input  logic [1:0]                        req_i,
   input  logic [1:0]                        we_i,
   input  logic [1:0][$clog2(NumWords)-1:0]  addr_i,
   input  logic [1:0][DataWidth-1:0]         wdata_i,
   input  logic [1:0][(DataWidth+7)/8-1:0]   be_i,
   output logic [1:0][DataWidth-1:0]         rdata_o,
   input  logic [1:0]                        inject_s_biterror_i,
   input  logic [1:0]                        inject_d_biterror_i
);

  localparam DataWidthAligned = ((DataWidth+7)/8)*8;
  localparam BeWidthAlgined   = (((DataWidth+7)/8+7)/8)*8;

  logic [1:0][DataWidthAligned-1:0]  wdata_aligned;
  logic [1:0][DataWidthAligned-1:0]  rdata_aligned;
  logic [1:0][BeWidthAlgined-1:0]    be_aligned, we;

  // align to 64 bits for inferable macro below
  always_comb begin : p_align
    for (int i = 0; i < 2; i++) begin
      wdata_aligned[i]                    = '0;
      be_aligned[i]                       = '0;
      wdata_aligned[i][DataWidth-1:0]     = wdata_i[i];
      be_aligned[i][BeWidthAlgined-1:0]   = be_i[i];

      rdata_o[i] = rdata_aligned[i][DataWidth-1:0];
    end
  end

  for (genvar i = 0; i < BeWidthAlgined; i++) begin
    assign we[0][i] = be_aligned[0][i] & we_i[0];
    assign we[1][i] = be_aligned[1][i] & we_i[1];
  end

  xpm_memory_tdpram #(
    // Common module parameters
    .MEMORY_SIZE        ( NumWords         ), // positive integer
    .MEMORY_PRIMITIVE   ( "auto"           ), // string; "auto", "distributed", "block" or "ultra";
    .CLOCKING_MODE      ( "common_clock"   ), // string; "common_clock", "independent_clock"
    .MEMORY_INIT_FILE   ( "none"           ), // string; "none" or "<filename>.mem"
    .MEMORY_INIT_PARAM  ( ""               ), // string;
    .USE_MEM_INIT       ( 0                ), // integer; 0,1
    .WAKEUP_TIME        ( "disable_sleep"  ), // string; "disable_sleep" or "use_sleep_pin"
    .MESSAGE_CONTROL    ( 0                ), // integer; 0,1
    .ECC_MODE           ( "no_ecc"         ), // string; "no_ecc", "encode_only", "decode_only" or "both_encode_and_decode"
    .AUTO_SLEEP_TIME    ( 0                ), // Do not Change
    // Port A module parameters
    .WRITE_DATA_WIDTH_A ( DataWidthAligned ), // positive integer
    .READ_DATA_WIDTH_A  ( DataWidthAligned ), // positive integer
    .BYTE_WRITE_WIDTH_A ( 8                ), // integer; 8, 9, or WRITE_DATA_WIDTH_A value
    .ADDR_WIDTH_A       ( $clog2(NumWords) ), // positive integer
    .READ_RESET_VALUE_A ( "0"              ), // string
    .READ_LATENCY_A     ( OutRegs + 1      ), // non-negative integer
    .WRITE_MODE_A       ( "no_change"      ), // string; "write_first", "read_first", "no_change"
    // Port B module parameters
    .WRITE_DATA_WIDTH_B ( DataWidthAligned ), // positive integer
    .READ_DATA_WIDTH_B  ( DataWidthAligned ), // positive integer
    .BYTE_WRITE_WIDTH_B ( 8                ), // integer; 8, 9, or WRITE_DATA_WIDTH_B value
    .ADDR_WIDTH_B       ( $clog2(NumWords) ), // positive integer
    .READ_RESET_VALUE_B ( "0"              ), // vector of READ_DATA_WIDTH_B bits
    .READ_LATENCY_B     ( OutRegs + 1      ), // non-negative integer
    .WRITE_MODE_B       ( "no_change"      )  // string; "write_first", "read_first", "no_change"
  ) i_xpm_memory_tdpram (
    .sleep          ( 1'b0                   ),
    .clka           ( clk_i                  ),
    .rsta           ( ~rst_ni                ),
    .ena            ( req_i[0]               ),
    .regcea         ( 1'b1                   ),
    .wea            ( we[0]                  ),
    .addra          ( addr_i[0]              ),
    .dina           ( wdata_aligned[0]       ),
    .injectsbiterra ( inject_s_biterror_i[0] ),
    .injectdbiterra ( inject_d_biterror_i[0] ),
    .douta          ( rdata_aligned[0]       ),
    .sbiterra       (                        ),
    .dbiterra       (                        ),
    .clkb           ( clk_i                  ),
    .rstb           ( ~rst_ni                ),
    .enb            ( req_i[1]               ),
    .regceb         ( 1'b1                   ),
    .web            ( we[1]                  ),
    .addrb          ( addr_i[1]              ),
    .dinb           ( wdata_aligned[1]       ),
    .injectsbiterrb ( inject_s_biterror_i[1] ),
    .injectdbiterrb ( inject_d_biterror_i[1] ),
    .doutb          ( rdata_aligned[1]       ),
    .sbiterrb       (                        ),
    .dbiterrb       (                        )
  );

endmodule
