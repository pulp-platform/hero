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
// Create Date:    01/01/2019                                                 //
// Design Name:    FPU_INTERCONNECT                                           //
// Module Name:    FPU_clock_gating                                           //
// Project Name:   VEGA                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:                                                               //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 06/07/2011 : File Created                                  //
//                                                                            //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module FPU_clock_gating
#(
   parameter int unsigned NB_FPU    = 1,
   parameter int unsigned NB_FPNEW  = 4
)
(
   input logic                   clk,
   input logic                   rst_n,

   input logic                   automatic_clock_gate_enable_i,

   input logic [NB_FPU-1:0]      fpu_req_in_i,
   input logic [NB_FPU-1:0]      fpu_gnt_out_i,
   input logic [NB_FPU-1:0]      fpu_rvalid_out_i,

   input logic [NB_FPNEW-1:0]    fpnew_req_in_i,
   input logic [NB_FPNEW-1:0]    fpnew_gnt_out_i,
   input logic [NB_FPNEW-1:0]    fpnew_rvalid_out_i,

   output logic [NB_FPU-1:0]     fpu_clock_gate_enable_o,
   output logic [NB_FPNEW-1:0]   fpnew_clock_gate_enable_o
);



   logic [NB_FPU-1:0][2:0]       pending_fpu;
   logic [NB_FPNEW-1:0][2:0]     pending_fpnew;

   always_ff @(posedge clk or negedge rst_n)
   begin : proc_CLOCK_GATE
      if(~rst_n) 
      begin
          pending_fpu   <= '0;
          pending_fpnew <= '0;
      end 
      else 
      begin
         
         for(int unsigned i=0; i<NB_FPU; i++)
         begin
            case({fpu_req_in_i[i] & fpu_gnt_out_i[i], fpu_rvalid_out_i[i]})
               2'b00, 2'b11: pending_fpu[i] <= pending_fpu[i];
               2'b10: pending_fpu[i] <= pending_fpu[i] + 1;
               2'b01: pending_fpu[i] <= pending_fpu[i] - 1;
            endcase // {fpu_req_in_i[i] & fpu_gnt_out_i[i], fpu_rvalid_out_i}
         end

         for(int unsigned i=0; i<NB_FPNEW; i++)
         begin
            case({fpnew_req_in_i[i] & fpnew_gnt_out_i[i], fpnew_rvalid_out_i[i]})
               2'b00, 2'b11: pending_fpnew[i] <= pending_fpnew[i];
               2'b10: pending_fpnew[i] <= pending_fpnew[i] + 1;
               2'b01: pending_fpnew[i] <= pending_fpnew[i] - 1;
            endcase // {fpnew_req_in_i[i] & fpnew_gnt_out_i[i], fpnew_rvalid_out_i}
         end

      end
   end


   always_comb
   begin
      if(automatic_clock_gate_enable_i == 1'b0)
      begin
         fpu_clock_gate_enable_o   = '1;
         fpnew_clock_gate_enable_o = '1;
      end
      else
      begin

         for(int unsigned i=0; i<NB_FPU; i++)
         begin
               fpu_clock_gate_enable_o[i] = (fpu_req_in_i[i]) ? 1'b1 : ( pending_fpu[i] != 0 );
         end

         for(int unsigned i=0; i<NB_FPNEW; i++)
         begin
               fpnew_clock_gate_enable_o[i] = (fpnew_req_in_i[i]) ? 1'b1 : ( pending_fpnew[i] != 0 );
         end

      end
   end

endmodule