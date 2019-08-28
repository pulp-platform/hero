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
// Module Name:    prefetcher_if                                              //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    This Block is in charge to generate consecutive fetch      //
//                 requests to PF cache controller, in order to warm-up the   //
//                 cache. The request are sent in the form of starting addr   //
//                 and number of cache line to be prefetched. Once the pref   //
//                 is triggered, this block will assert all these fetch       //
//                 requests.                                                  //
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


module prefetcher_if
#(
   parameter DATA_DEPTH = 4
)
(
   input logic                              clk,
   input logic                              rst_n,
   input logic                              test_en_i,

   // Interface from HW PF control Unit
   input  logic [31:0]                      pf_addr_i,
   input  logic [7:0]                       pf_size_i,
   input  logic                             pf_req_i,
   output logic                             pf_ack_o,
   output logic                             pf_done_o,


   // interface to private prefetch cache controller
   output logic                             pf_req_o,
   output logic [31:0]                      pf_addr_o,
   input  logic                             pf_gnt_i,
   input  logic                             pf_rvalid_i
);


   enum logic {IDLE, SW_PF_REQ }     CS, NS;
   logic [31:0]                      counter_CS, counter_NS;
   logic                             sample_pf_addr, update_pf_addr;
   logic [31:0]                      pf_addr_Q;
   logic [7:0]                       pf_size_Q;


   logic [31:0]                      pf_addr_int;
   logic [7:0]                       pf_size_int;
   logic                             pf_req_int;
   logic                             pf_ack_int;
   


   always_ff @(posedge clk or negedge rst_n)
   begin : proc_seq_CS
      if(~rst_n)
      begin
         CS <= IDLE;
         counter_CS <= '0;
         pf_addr_Q  <= '0;
         pf_size_Q  <= '0;
      end
      else
      begin
         CS <= NS;
         counter_CS <= counter_NS;

         if(sample_pf_addr)
         begin
            pf_addr_Q <= { pf_addr_int[31:4] , 4'b0000 };
            pf_size_Q <= pf_size_int;
         end
         else
         begin
            if (update_pf_addr)
            begin
               pf_addr_Q <= pf_addr_Q + 8'h10; // FIXME hard coded (one cache line is loaded)
               pf_size_Q <= pf_size_Q - 1'b1;
            end
         end
      end
   end


   always_comb
   begin : proc_comb_FSM
      sample_pf_addr = 1'b0;
      update_pf_addr = 1'b0;
      pf_ack_int     = 1'b0;
      NS             = CS;
      counter_NS     = counter_CS;
      pf_req_o       = 1'b0;
      pf_addr_o      = '0;
      pf_done_o      = 1'b0;


      case(CS)
      IDLE: 
      begin
         sample_pf_addr = pf_req_int;
         pf_ack_int       = 1'b1;

         if(pf_req_int)
            NS = SW_PF_REQ;
         else
            NS = IDLE;
      end

      SW_PF_REQ:
      begin
         pf_req_o = 1'b1;
         pf_addr_o = pf_addr_Q;

         if(pf_size_Q == 0)
         begin
            NS = (pf_gnt_i) ? IDLE : SW_PF_REQ;
            update_pf_addr = 1'b0;
            
            if(pf_gnt_i)
                pf_done_o = (pf_req_int == 1'b0) ? 1'b1 : 1'b0;
            else
                pf_done_o = 1'b0;
         end
         else
         begin
            update_pf_addr = pf_gnt_i;
            NS = SW_PF_REQ;
         end
      end


      default:
      begin
         NS = IDLE;
      end


      endcase // CS
   
   end

   //////////////////////////////////////////////////////////////////////////////////////
   //  ██████╗███╗   ███╗██████╗     ██████╗ ██╗   ██╗███████╗███████╗███████╗██████╗  //
   // ██╔════╝████╗ ████║██╔══██╗    ██╔══██╗██║   ██║██╔════╝██╔════╝██╔════╝██╔══██╗ //
   // ██║     ██╔████╔██║██║  ██║    ██████╔╝██║   ██║█████╗  █████╗  █████╗  ██████╔╝ //
   // ██║     ██║╚██╔╝██║██║  ██║    ██╔══██╗██║   ██║██╔══╝  ██╔══╝  ██╔══╝  ██╔══██╗ //
   // ╚██████╗██║ ╚═╝ ██║██████╔╝    ██████╔╝╚██████╔╝██║     ██║     ███████╗██║  ██║ //
   //  ╚═════╝╚═╝     ╚═╝╚═════╝     ╚═════╝  ╚═════╝ ╚═╝     ╚═╝     ╚══════╝╚═╝  ╚═╝ //
   //////////////////////////////////////////////////////////////////////////////////////
   generic_fifo
   #(
      .DATA_WIDTH ( 32+8            ),
      .DATA_DEPTH ( DATA_DEPTH      )
   )
   pref_cmd_buffer
   (
      .clk           ( clk                          ),
      .rst_n         ( rst_n                        ),

      .data_i        ( {pf_size_i, pf_addr_i}       ),
      .valid_i       ( pf_req_i                     ),
      .grant_o       ( pf_ack_o                     ),

      .data_o        ( {pf_size_int, pf_addr_int}   ),
      .valid_o       ( pf_req_int                   ),
      .grant_i       ( pf_ack_int                   ),

      .test_mode_i   ( test_en_i                    )
   );


endmodule
