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
// Module Name:    RoutingBlock_2ch_Req_icache_intc.sv                        //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:   Block that embeds the arbitration/routing tree and the      //
//                decoding logic for the response coming from the memory side.//
//                It is used when N_AUX_CHANNEL is > 0                        //
//                                                                            //
// Revision v0.1 - 16/02/2018 : File Created                                  //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module RoutingBlock_2ch_Req_icache_intc
#(
    parameter int unsigned ADDRESS_WIDTH = 32,
    parameter int unsigned N_CORES       = 16,
    parameter int unsigned N_AUX_CHANNEL = 1,
    parameter int unsigned UID_WIDTH     = N_CORES+N_AUX_CHANNEL,
    parameter int unsigned N_CACHE_BANKS = 8,
    parameter int unsigned DATA_WIDTH    = 32
)
(
    input  logic                                                 clk_i,
    input  logic                                                 rst_ni,

    output logic                                                 request_o,
    output logic [ADDRESS_WIDTH-1:0]                             address_o,
    output logic [UID_WIDTH-1:0]                                 UID_o,
    input  logic                                                 grant_i,

    input  logic [N_CORES+N_AUX_CHANNEL-1:0]                     request_i,
    input  logic [N_CORES+N_AUX_CHANNEL-1:0][ADDRESS_WIDTH-1:0]  address_i,
    input  logic [N_CORES+N_AUX_CHANNEL-1:0][UID_WIDTH-1:0]      UID_i,
    output logic [N_CORES+N_AUX_CHANNEL-1:0]                     grant_o,

    input   logic                                                response_i,
    input   logic [UID_WIDTH-1:0]                                response_UID_i,
    output  logic [N_CORES+N_AUX_CHANNEL-1:0]                    response_o
);
   assign response_o = {UID_WIDTH{response_i}} & response_UID_i;

   logic                                   request_core;
   logic [ADDRESS_WIDTH-1:0]               address_core;
   logic [UID_WIDTH-1:0]                   UID_core;
   logic                                   grant_core;

   logic                                   request_aux;
   logic [ADDRESS_WIDTH-1:0]               address_aux;
   logic [UID_WIDTH-1:0]                   UID_aux;
   logic                                   grant_aux;

   logic [$clog2(N_CORES+N_AUX_CHANNEL)-1:0] arb_FLAG;


   generate
      if(N_CORES > 1)
      begin : MULTI_CORE
         DistributedArbitrationNetwork_Req_icache_intc #( .ADDRESS_WIDTH (ADDRESS_WIDTH), .UID_WIDTH(UID_WIDTH), .N_CORES(N_CORES) )  DistributedArbitrationNetwork_Req_icache_intc_i
         ( 
            .clk_i        ( clk_i                     ),
            .rst_ni       ( rst_ni                    ),
            
            .request_i    ( request_i [N_CORES-1:0]   ),
            .address_i    ( address_i [N_CORES-1:0]   ),
            .UID_i        ( UID_i     [N_CORES-1:0]   ),
            .grant_o      ( grant_o   [N_CORES-1:0]   ),

            .request_o    ( request_core              ),
            .address_o    ( address_core              ),
            .UID_o        ( UID_core                  ),
            .grant_i      ( grant_core                )
         );
      end
      else
      begin : SINGLE_CORE
         assign request_core   = request_i [N_CORES-1:0];
         assign address_core   = address_i [N_CORES-1:0];
         assign UID_core       = UID_i     [N_CORES-1:0];
         assign grant_o[N_CORES-1:0]        = grant_core;
      end


      if(N_AUX_CHANNEL > 1)
      begin : MULTI_AUX
         DistributedArbitrationNetwork_Req_icache_intc #( .ADDRESS_WIDTH (ADDRESS_WIDTH), .UID_WIDTH(UID_WIDTH), .N_CORES(N_AUX_CHANNEL) )  DistributedArbitrationNetwork_Req_icache_intc_i
         ( 
            .clk_i        ( clk_i                                         ),
            .rst_ni       ( rst_ni                                        ),
            
            .request_i    ( request_i [N_CORES+N_AUX_CHANNEL-1:N_CORES]   ),
            .address_i    ( address_i [N_CORES+N_AUX_CHANNEL-1:N_CORES]   ),
            .UID_i        ( UID_i     [N_CORES+N_AUX_CHANNEL-1:N_CORES]   ),
            .grant_o      ( grant_o   [N_CORES+N_AUX_CHANNEL-1:N_CORES]   ),

            .request_o    ( request_aux                                   ),
            .address_o    ( address_aux                                   ),
            .UID_o        ( UID_aux                                       ),
            .grant_i      ( grant_aux                                     )
         );
      end
      else
      begin : SINGLE_AUX
         assign request_aux   = request_i [N_CORES+N_AUX_CHANNEL-1:N_CORES];
         assign address_aux   = address_i [N_CORES+N_AUX_CHANNEL-1:N_CORES];
         assign UID_aux       = UID_i     [N_CORES+N_AUX_CHANNEL-1:N_CORES];
         assign grant_o[N_CORES+N_AUX_CHANNEL-1:N_CORES]       = grant_aux;
      end



      logic Priority;
      assign Priority = (arb_FLAG < N_AUX_CHANNEL );

      lint_mux 
      #(
         .ADDR_WIDTH ( ADDRESS_WIDTH ),
         .UID_WIDTH  ( UID_WIDTH     )
      )
      AUX_MUX
      (
         .arb_flag_i   ( Priority ),        
         // LEFT SIDE
         .instr_add0_i ( address_core ),
         .instr_add1_i ( address_aux  ),
         .instr_req0_i ( request_core ),
         .instr_req1_i ( request_aux  ),
         .instr_ID0_i  ( UID_core     ),
         .instr_ID1_i  ( UID_aux      ),     
         .instr_gnt0_o ( grant_core   ),
         .instr_gnt1_o ( grant_aux    ),    

         .instr_add_o  ( address_o    ),
         .instr_req_o  ( request_o    ),
         .instr_ID_o   ( UID_o        ),          
         .instr_gnt_i  ( grant_i      )
      );



       // Rotating Priority: Count N_CORE + N_AUX (eg 8 and 1)
       // 0 --> 1 --> PRI on AUX
       // 1 --> 0 --> PRI on CH0
       // 2 --> 0 --> PRI on CH0
       // 3 --> 0 --> PRI on CH0
       // 4 --> 0 --> PRI on CH0
       // 5 --> 0 --> PRI on CH0
       // 6 --> 0 --> PRI on CH0
       // 7 --> 0 --> PRI on CH0
       // 8 --> 0 --> PRI on CH0

       always_ff @(posedge clk_i or negedge rst_ni)
       begin
           if(rst_ni == 1'b0)
              arb_FLAG <= '0;
           else
               if( request_o  & grant_i )
               begin
                     if(arb_FLAG<N_CORES+N_AUX_CHANNEL)
                        arb_FLAG <= arb_FLAG + 1'b1;
                     else
                        arb_FLAG <= '0;
               end
       end





   endgenerate

endmodule
