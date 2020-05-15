// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module register_file_1r_1w_test_wrap
#(
    parameter ADDR_WIDTH    = 5,
    parameter DATA_WIDTH    = 32
)
(
    input  logic                                  clk,

    input  logic                                  test_en_i,

    // Read port
    input  logic                                  ReadEnable,
    input  logic [ADDR_WIDTH-1:0]                 ReadAddr,
    output logic [DATA_WIDTH-1:0]                 ReadData,


    // Write port
    input  logic                                  WriteEnable,
    input  logic [ADDR_WIDTH-1:0]                 WriteAddr,
    input  logic [DATA_WIDTH-1:0]                 WriteData

);

   register_file_1r_1w
   #(
       .ADDR_WIDTH  ( ADDR_WIDTH ),
       .DATA_WIDTH  ( DATA_WIDTH )
   )
   register_file_1r_1w_i
   (
      .clk          ( clk ),

      .test_en_i,

      .ReadEnable   ( ReadEnable  ),
      .ReadAddr     ( ReadAddr    ),
      .ReadData     ( ReadData    ),

      .WriteEnable  ( WriteEnable ),
      .WriteAddr    ( WriteAddr   ),
      .WriteData    ( WriteData   )
   );

endmodule // register_file_1r_1w_test_wrap
