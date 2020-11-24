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
// Description: Single Ported SRAM
//
module sp_sram #(
    parameter int unsigned DataWidth = 64,
    parameter int unsigned NumWords  = 1024,
    parameter bit          OutRegs   = 0,   // enables output registers in FPGA macro (read lat = 2)
    parameter logic [1:0]  SimInit   = 0    // no-effect here
)(
   input  logic                         clk_i,
   input  logic                         rst_ni,
   input  logic                         req_i,
   input  logic                         we_i,
   input  logic [$clog2(NumWords)-1:0]  addr_i,
   input  logic [DataWidth-1:0]         wdata_i,
   input  logic [(DataWidth+7)/8-1:0]   be_i,
   output logic [DataWidth-1:0]         rdata_o,
   input  logic                         inject_s_biterror_i,
   input  logic                         inject_d_biterror_i
);

  localparam DataWidthAligned = ((DataWidth+7)/8)*8;
  localparam BeWidthAlgined   = (((DataWidth+7)/8+7)/8)*8;

  logic [DataWidthAligned-1:0]  wdata_aligned;
  logic [DataWidthAligned-1:0]  rdata_aligned;
  logic [BeWidthAlgined-1:0]    be_aligned, we;

  // align to 64 bits for inferable macro below
  always_comb begin : p_align
      wdata_aligned                    = '0;
      be_aligned                       = '0;
      wdata_aligned[DataWidth-1:0]     = wdata_i;
      be_aligned[BeWidthAlgined-1:0]   = be_i;

      rdata_o = rdata_aligned[DataWidth-1:0];
  end

  for (genvar i = 0; i < BeWidthAlgined; i++) begin
    assign we[i] = be_aligned[i] & we_i;
  end

  xpm_memory_spram #(
    // Common module parameters
    .MEMORY_SIZE        ( NumWords         ), // positive integer
    .MEMORY_PRIMITIVE   ( "auto"           ), // string; "auto", "distributed", "block" or "ultra";
    .MEMORY_INIT_FILE   ( "none"           ), // string; "none" or "<filename>.mem"
    .MEMORY_INIT_PARAM  ( ""               ), // string;
    .USE_MEM_INIT       ( 0                ), // integer; 0,1
    .WAKEUP_TIME        ( "disable_sleep"  ), // string; "disable_sleep" or "use_sleep_pin"
    .MESSAGE_CONTROL    ( 0                ), // integer; 0,1
    // Port A module parameters
    .WRITE_DATA_WIDTH_A ( DataWidthAligned ), // positive integer
    .READ_DATA_WIDTH_A  ( DataWidthAligned ), // positive integer
    .BYTE_WRITE_WIDTH_A ( 8                ), // integer; 8, 9, or WRITE_DATA_WIDTH_A value
    .ADDR_WIDTH_A       ( $clog2(NumWords) ), // positive integer
    .READ_RESET_VALUE_A ( "0"              ), // string
    .ECC_MODE           ( "no_ecc"         ), // string; "no_ecc", "encode_only", "decode_only" or "both_encode_and_decode"
    .AUTO_SLEEP_TIME    ( 0                ), // Do not Change
    .READ_LATENCY_A     ( OutRegs + 1      ), // non-negative integer
    .WRITE_MODE_A       ( "read_first"     )  // string; "write_first", "read_first", "no_change"
  ) i_xpm_memory_spram (
    // Common module ports
    .sleep         (1'b0               ),

    // Port A module ports
    .clka          (clk_i              ),
    .rsta          (~rst_ni            ),
    .ena           (req_i              ),
    .regcea        (1'b1               ),
    .wea           (we                 ),
    .addra         (addr_i             ),
    .dina          (wdata_aligned      ),
    .injectsbiterra(inject_s_biterror_i),
    .injectdbiterra(inject_d_biterror_i),
    .douta         (rdata_aligned      ),
    .sbiterra      (                   ),
    .dbiterra      (                   )
  );

endmodule
