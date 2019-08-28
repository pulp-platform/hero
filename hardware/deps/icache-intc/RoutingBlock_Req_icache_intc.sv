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
// Module Name:    RoutingBlock_Req_icache_intc.sv                            //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:   Block that embeds the arbitration/routing tree and the      //
//                decoding logic for the response coming from the memory side //
//                                                                            //
// Revision v0.1 - 16/02/2018 : File Created                                  //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module RoutingBlock_Req_icache_intc
#(
    parameter int unsigned ADDRESS_WIDTH = 32,
    parameter int unsigned N_CORES       = 16,
    parameter int unsigned UID_WIDTH     = N_CORES,
    parameter int unsigned N_CACHE_BANKS = 8,
    parameter int unsigned DATA_WIDTH    = 32
)
(
    input  logic                                   clk_i,
    input  logic                                   rst_ni,

    output logic                                   request_o,
    output logic [ADDRESS_WIDTH-1:0]               address_o,
    output logic [UID_WIDTH-1:0]                   UID_o,
    input  logic                                   grant_i,

    input  logic [N_CORES-1:0]                     request_i,
    input  logic [N_CORES-1:0][ADDRESS_WIDTH-1:0]  address_i,
    input  logic [N_CORES-1:0][UID_WIDTH-1:0]      UID_i,
    output logic [N_CORES-1:0]                     grant_o,

    input   logic                                  response_i,
    input   logic [UID_WIDTH-1:0]                  response_UID_i,
    output  logic [N_CORES-1:0]                    response_o
);
   assign response_o = {UID_WIDTH{response_i}} & response_UID_i;

   generate
      if(N_CORES > 1)
      begin : MULTI_CORE
         DistributedArbitrationNetwork_Req_icache_intc #( .ADDRESS_WIDTH (ADDRESS_WIDTH), .UID_WIDTH(UID_WIDTH), .N_CORES(N_CORES) )  DistributedArbitrationNetwork_Req_icache_intc_i
         (
            .clk_i        ( clk_i       ),
            .rst_ni       ( rst_ni      ),
            .request_i    ( request_i   ),
            .address_i    ( address_i   ),
            .UID_i        ( UID_i       ),
            .grant_o      ( grant_o     ),
            .request_o    ( request_o   ),
            .address_o    ( address_o   ),
            .UID_o        ( UID_o       ),
            .grant_i      ( grant_i     )
         );
      end
      else
      begin : SINGLE_CORE
         assign request_o   = request_i;
         assign address_o   = address_i;
         assign UID_o       = UID_i;
         assign grant_o     = grant_i;
      end
   endgenerate

endmodule
