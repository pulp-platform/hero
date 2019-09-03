// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Company:        Micrel Lab @ DEIS - University of Bologna                  //
//                    Viale Risorgimento 2 40136                              //
//                    Bologna - fax 0512093785 -                              //
//                                                                            //
// Engineer:       Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    22/01/2018                                                 //
// Design Name:    icache_intc                                                //
// Module Name:    Req_Arb_Node_icache_intc.sv                                //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:   Distributed routing and arbitration tree block, build       //
//                usign fan_in primities (2x1 routing blocks)                 //
//                                                                            //
// Revision v0.1 - 16/02/2018 : File Created                                  //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module Req_Arb_Node_icache_intc
#(
   parameter ADDRESS_WIDTH = 32, 
   parameter UID_WIDTH     = 16
)
(
   // IN PORT 0
   input  logic                     request_ch0_i,
   input  logic [ADDRESS_WIDTH-1:0] address_ch0_i,
   input  logic [UID_WIDTH-1:0]     UID_ch0_i,
   output logic                     grant_ch0_o,
   // IN PORT 1
   input  logic                     request_ch1_i,
   input  logic [ADDRESS_WIDTH-1:0] address_ch1_i,
   input  logic [UID_WIDTH-1:0]     UID_ch1_i,
   output logic                     grant_ch1_o,
   // OUT PORT
   output logic [ADDRESS_WIDTH-1:0] address_o,
   output logic                     request_o,
   output logic [UID_WIDTH-1:0]     UID_o,
   input  logic                     grant_i,
   // FLAG to switch priority
   input logic                      Flag_i
);

   logic      ch_selector;  // 0 --> CH0; 1 --> CH1
   always_comb
   begin
      request_o   =  request_ch0_i |   request_ch1_i;
      ch_selector = ~request_ch0_i | ( Flag_i & request_ch1_i );
      grant_ch0_o = (( request_ch0_i & ~request_ch1_i) | ( request_ch0_i & ~Flag_i)) & grant_i;
      grant_ch1_o = ((~request_ch0_i &  request_ch1_i) | ( request_ch1_i &  Flag_i)) & grant_i;    
      case(ch_selector)
         1'b1: begin address_o   = address_ch1_i; UID_o    = UID_ch1_i; end
         1'b0: begin address_o   = address_ch0_i; UID_o    = UID_ch0_i; end
      endcase
   end
 
endmodule
