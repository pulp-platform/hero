// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Antonio Pullini - pullinia@iis.ee.ethz.ch                  //
//                                                                            //
// Additional contributions by:                                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    RISC-V register file  Wrapper                              //
// Project Name:   RISCV                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Register file Wrapper, that provides one test port (1RW)   //
//                 to be connected to a bist collar (MBIST)                   //
//                 Test data is written on port A, (port B is masked during   //
//                 test. Test Read data is got from port A (rdata_a_o)        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

//
// ADDRESS 0 is NOT WRITABLE !!!!!!!!!!!!!!!!!!!!
//

module register_file_test_wrap
#(
   parameter ADDR_WIDTH    = 5,
   parameter DATA_WIDTH    = 32,
   parameter FPU           = 0,
   parameter Zfinx         = 0
)
(
   // Clock and Reset
   input  logic                   clk,
   input  logic                   rst_n,

   input  logic                   test_en_i,

   //Read port R1
   input  logic [ADDR_WIDTH-1:0]  raddr_a_i,
   output logic [DATA_WIDTH-1:0]  rdata_a_o,

   //Read port R2
   input  logic [ADDR_WIDTH-1:0]  raddr_b_i,
   output logic [DATA_WIDTH-1:0]  rdata_b_o,

   //Read port R3
   input  logic [ADDR_WIDTH-1:0]  raddr_c_i,
   output logic [DATA_WIDTH-1:0]  rdata_c_o,

   // Write port W1
   input  logic [ADDR_WIDTH-1:0]   waddr_a_i,
   input  logic [DATA_WIDTH-1:0]   wdata_a_i,
   input  logic                    we_a_i,

   // Write port W2
   input  logic [ADDR_WIDTH-1:0]   waddr_b_i,
   input  logic [DATA_WIDTH-1:0]   wdata_b_i,
   input  logic                    we_b_i
);




   riscv_register_file
   #(
      .ADDR_WIDTH ( ADDR_WIDTH          ),
      .DATA_WIDTH ( DATA_WIDTH          ),
      .FPU        ( FPU                 ),
      .Zfinx      ( Zfinx               )
   )
   riscv_register_file_i
   (
      .clk        ( clk                 ),
      .rst_n      ( rst_n               ),

      .test_en_i  ( test_en_i           ),

      .raddr_a_i  ( raddr_a_i           ),
      .rdata_a_o  ( rdata_a_o           ),

      .raddr_b_i  ( raddr_b_i           ),
      .rdata_b_o  ( rdata_b_o           ),

      .raddr_c_i  ( raddr_c_i           ),
      .rdata_c_o  ( rdata_c_o           ),

      .waddr_a_i  ( waddr_a_i           ),
      .wdata_a_i  ( wdata_a_i           ),
      .we_a_i     ( we_a_i              ),

      .waddr_b_i  ( waddr_b_i           ),
      .wdata_b_i  ( wdata_b_i           ),
      .we_b_i     ( we_b_i              )
   );





endmodule
