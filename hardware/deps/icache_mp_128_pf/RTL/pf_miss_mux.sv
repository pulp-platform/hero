////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Copyright 2018 ETH Zurich and University of Bologna.                       //
// Copyright and related rights are licensed under the Solderpad Hardware     //
// License, Version 0.51 (the "License"); you may not use this file except in //
// compliance with the License.  You may obtain a copy of the License at      //
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law  //
// or agreed to in writing, software, hardware and materials distributed under//
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR     //
// CONDITIONS OF ANY KIND, either express or implied. See the License for the //
// specific language governing permissions and limitations under the License. //
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
// Design Name:    ICACHE_MP_128_PF                                           //
// Module Name:    pf_miss_mux                                                //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    This block mupltiplex two different request, from HW PF    //
//                 and from multiplexed request from icache intc side.        //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 22/01/2018 : File Created                                  //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module pf_miss_mux 
#(
   parameter ADDR_WIDTH = 32, 
   parameter ID_WIDTH   = 16
)
(
   input logic                    arb_flag_i,        
   // LEFT SIDE
   input  logic [ADDR_WIDTH-1:0]  instr_add0_i,
   input  logic [ADDR_WIDTH-1:0]  instr_add1_i,
   input  logic                   instr_req0_i,
   input  logic                   instr_req1_i,
   input  logic [ID_WIDTH-1:0]    instr_ID0_i,
   input  logic [ID_WIDTH-1:0]    instr_ID1_i,     
   output logic                   instr_gnt0_o,
   output logic                   instr_gnt1_o,    

   // RIGTH SIDE
   output logic [ADDR_WIDTH-1:0]  instr_add_o,
   output logic                   instr_req_o,
   output logic [ID_WIDTH-1:0]    instr_ID_o,          
   input  logic                   instr_gnt_i

);

   logic   mux_sel;

   //Mupltiplexer
   always_comb
   begin : two_Way_Mux
      case(mux_sel) //synopsys full_case
         1'b0:
         begin //PRIORITY ON CH_0
            instr_add_o   = instr_add0_i;
            instr_ID_o    = instr_ID0_i;
         end

         1'b1:
         begin //PRIORITY ON CH_1
            instr_add_o   = instr_add1_i;
            instr_ID_o    = instr_ID1_i;
         end

      endcase
   end
        
   assign instr_req_o  =     instr_req0_i | instr_req1_i;
   assign mux_sel      =    ~instr_req0_i | ( arb_flag_i & instr_req1_i);   // Sel FOR ROUND ROBIN MUX

   // Grant gnt_0 and gnt_1
   assign instr_gnt0_o      =    (( instr_req0_i & ~instr_req1_i) | ( instr_req0_i & ~arb_flag_i)) & instr_gnt_i;
   assign instr_gnt1_o      =    ((~instr_req0_i &  instr_req1_i) | ( instr_req1_i &  arb_flag_i)) & instr_gnt_i;
   
endmodule
