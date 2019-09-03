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
// Module Name:    icache_intc.sv                                             //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:   top_level, that instanciates the routing and response       //
//                blocks. It is fully parametric, and it is possible to       //
//                to have N+M Channels where M and N are integers, powerof 2  //
//                fair arbitration is provided through distrubuted Round      //
//                robin arbiters.                                             //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 16/02/2018 : File Created                                  //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


module icache_intc 
#(
    parameter ADDRESS_WIDTH  = 32,
    parameter N_CORES        = 8,
    parameter N_AUX_CHANNEL  = 0,
    parameter UID_WIDTH      = N_CORES+N_AUX_CHANNEL,
    parameter DATA_WIDTH     = 32,
    parameter N_CACHE_BANKS  = 16,
    parameter OFFSET         = $clog2(DATA_WIDTH)-3
)
(
   input  logic                                                      clk_i,
   input  logic                                                      rst_ni,

   input  logic [N_CORES+N_AUX_CHANNEL-1:0]                          request_i,
   input  logic [N_CORES+N_AUX_CHANNEL-1:0][ADDRESS_WIDTH-1:0]       address_i,
   output logic [N_CORES+N_AUX_CHANNEL-1:0]                          grant_o,
   output logic [N_CORES+N_AUX_CHANNEL-1:0]                          response_o,
   output logic [N_CORES+N_AUX_CHANNEL-1:0][DATA_WIDTH-1:0]          read_data_o,

   output logic [N_CACHE_BANKS-1:0]                                  request_o,
   output logic [N_CACHE_BANKS-1:0][ADDRESS_WIDTH-1:0]               address_o,
   output logic [N_CACHE_BANKS-1:0][UID_WIDTH-1:0]                   UID_o,
   input  logic [N_CACHE_BANKS-1:0]                                  grant_i,

   input  logic [N_CACHE_BANKS-1:0][DATA_WIDTH-1:0]                  read_data_i,
   input  logic [N_CACHE_BANKS-1:0]                                  response_i,
   input  logic [N_CACHE_BANKS-1:0][UID_WIDTH-1:0]                   response_UID_i
);
   localparam DEST_WIDTH  = (N_CACHE_BANKS == 1) ? 1'b1 : $clog2(N_CACHE_BANKS);

   logic [N_CORES+N_AUX_CHANNEL-1:0][UID_WIDTH-1:0]   UID_int;
   logic [N_CORES+N_AUX_CHANNEL-1:0]                  grant_from_CB     [N_CACHE_BANKS-1:0];

   logic [N_CACHE_BANKS-1:0]                          request_from_CORE [N_CORES+N_AUX_CHANNEL-1:0];
   logic [N_CORES+N_AUX_CHANNEL-1:0]                  response_from_CB  [N_CACHE_BANKS-1:0];
   logic [N_CACHE_BANKS-1:0]                          response_to_CORE  [N_CORES+N_AUX_CHANNEL-1:0];
   logic [N_CORES+N_AUX_CHANNEL-1:0]                  request_to_CB     [N_CACHE_BANKS-1:0];
   logic [N_CACHE_BANKS-1:0]                          grant_to_CORE     [N_CORES+N_AUX_CHANNEL-1:0];
   logic [N_CORES+N_AUX_CHANNEL-1:0][DEST_WIDTH-1:0]  destination;

   genvar j,k;
   generate
      for (k=0; k<N_CORES+N_AUX_CHANNEL; k++)
      begin : Destination_blk
         if(N_CACHE_BANKS == 1)
            assign destination[k] = 1'b0;
         else
            assign destination[k] = address_i[k][OFFSET+$clog2(N_CACHE_BANKS)-1:OFFSET];

         for (j=0; j<N_CACHE_BANKS; j++)
         begin : Swapping
            assign response_to_CORE[k][j] = response_from_CB[j][k];
            assign request_to_CB[j][k]    = request_from_CORE[k][j];
            assign grant_to_CORE[k][j]    = grant_from_CB[j][k];
         end
      end

      for (j=0; j<N_CACHE_BANKS; j++)
      begin : RoutingRequestNetwork
         if(N_AUX_CHANNEL == 0)
         begin : NO_AUX_CHANNEL
            RoutingBlock_Req_icache_intc #( .ADDRESS_WIDTH(ADDRESS_WIDTH), .N_CORES(N_CORES), .UID_WIDTH(UID_WIDTH), .N_CACHE_BANKS(N_CACHE_BANKS), .DATA_WIDTH(DATA_WIDTH)) RoutingBlock_Req_icache_intc_i
            (
               .clk_i          ( clk_i                ),
               .rst_ni         ( rst_ni               ),

               .request_o      ( request_o        [j] ),
               .address_o      ( address_o        [j] ),
               .UID_o          ( UID_o            [j] ),
               .grant_i        ( grant_i          [j] ),

               .request_i      ( request_to_CB    [j] ),
               .address_i      ( address_i            ),
               .UID_i          ( UID_int              ),
               .grant_o        ( grant_from_CB    [j] ),

               .response_i     ( response_i       [j] ),
               .response_UID_i ( response_UID_i   [j] ),
               .response_o     ( response_from_CB [j] )
            );
         end
         else
         begin : WITH_AUX_CH
               RoutingBlock_2ch_Req_icache_intc #( .ADDRESS_WIDTH(ADDRESS_WIDTH), .N_CORES(N_CORES), .N_AUX_CHANNEL(N_AUX_CHANNEL), .UID_WIDTH(UID_WIDTH), .N_CACHE_BANKS(N_CACHE_BANKS), .DATA_WIDTH(DATA_WIDTH)) RoutingBlock_Req_icache_intc_i
               (
                  .clk_i          ( clk_i                ),
                  .rst_ni         ( rst_ni               ),

                  .request_o      ( request_o        [j] ),
                  .address_o      ( address_o        [j] ),
                  .UID_o          ( UID_o            [j] ),
                  .grant_i        ( grant_i          [j] ),

                  .request_i      ( request_to_CB    [j] ),
                  .address_i      ( address_i            ),
                  .UID_i          ( UID_int              ),
                  .grant_o        ( grant_from_CB    [j] ),

                  .response_i     ( response_i       [j] ),
                  .response_UID_i ( response_UID_i   [j] ),
                  .response_o     ( response_from_CB [j] )
               );
         end
      end


      for (j=0; j<  N_CORES+N_AUX_CHANNEL; j++)
      begin : RoutingResponsetNetwork
         RoutingBlock_Resp_icache_intc #( .UID(2**j), .DEST_WIDTH(DEST_WIDTH), .N_CACHE_BANKS(N_CACHE_BANKS), .DATA_WIDTH(DATA_WIDTH), .UID_WIDTH(UID_WIDTH) ) RoutingBlock_Resp_icache_intc_i
         (
            .response_i    ( response_to_CORE  [j] ),
            .read_data_i   ( read_data_i           ),
            .response_o    ( response_o        [j] ),
            .read_data_o   ( read_data_o       [j] ),

            .request_i     ( request_i         [j] ),
            .destination_i ( destination       [j] ),
            .grant_o       ( grant_o           [j] ),
            .request_o     ( request_from_CORE [j] ),
            .grant_i       ( grant_to_CORE     [j] ),
            .UID_o         ( UID_int           [j] )
         );
      end
    endgenerate
endmodule
