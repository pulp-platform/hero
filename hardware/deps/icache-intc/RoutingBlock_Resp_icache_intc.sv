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
// Module Name:    RoutingBlock_Resp_icache_intc.sv                           //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:   Block that embeds the routing tree for the response side    //
//                and the decoding logic for the request coming from the      //
//                fetch side.                                                 //
//                                                                            //
// Revision v0.1 - 16/02/2018 : File Created                                  //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module RoutingBlock_Resp_icache_intc
#(
   parameter int unsigned UID_WIDTH       = 8,
   parameter int unsigned UID             = 1,
   parameter int unsigned N_CACHE_BANKS   = 16,
   parameter int unsigned DATA_WIDTH      = 32,
   parameter int unsigned DEST_WIDTH      = 1
)
(
   input logic [N_CACHE_BANKS-1:0]                 response_i,
   input logic [N_CACHE_BANKS-1:0][DATA_WIDTH-1:0] read_data_i,

   output logic                                    response_o,
   output logic [DATA_WIDTH-1:0]                   read_data_o,

   input logic                                     request_i,
   input logic [DEST_WIDTH-1:0]                    destination_i,
   output logic                                    grant_o,

   output logic [N_CACHE_BANKS-1:0]                request_o,
   input  logic [N_CACHE_BANKS-1:0]                grant_i,
   output logic [UID_WIDTH-1:0]                    UID_o    
);
   typedef logic [UID_WIDTH-1:0] logic_uid_type;

   DistributedArbitrationNetwork_Resp_icache_intc  #( .N_CACHE_BANKS(N_CACHE_BANKS), .DATA_WIDTH(DATA_WIDTH) )  DistributedArbitrationNetwork_Resp_icache_intc_i
   (
      .response_i  ( response_i  ),
      .read_data_i ( read_data_i ),
      .response_o  ( response_o  ),
      .read_data_o ( read_data_o )
   );


      // Decoding Logic
      always @(*)
      begin
         request_o = '0;
         request_o [destination_i] = request_i;
         grant_o                    = grant_i[destination_i];
         UID_o                      = logic_uid_type'(UID);
      end



endmodule
