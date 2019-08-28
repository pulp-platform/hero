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
// Module Name:    DistributedArbitrationNetwork_Req_icache_intc.sv           //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Block linked to memory side, that receives requests        //
//                 and arbitrates with RoundRobin Policy. It is Built using   //
//                 2x1 fan_in primitives, with distributed routing and        //
//                 arbitration                                                //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 16/02/2018 : File Created                                  //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module DistributedArbitrationNetwork_Req_icache_intc
#(
    parameter N_CORES       = 16,
    parameter ADDRESS_WIDTH = 32,
    parameter UID_WIDTH     = 20
) 
(
   input  logic                                   clk_i,
   input  logic                                   rst_ni,

   input  logic [N_CORES-1:0]                     request_i,
   input  logic [N_CORES-1:0][ADDRESS_WIDTH-1:0]  address_i,
   input  logic [N_CORES-1:0][UID_WIDTH-1:0]      UID_i,
   output logic [N_CORES-1:0]                     grant_o,

   output logic                                   request_o,
   output logic [ADDRESS_WIDTH-1:0]               address_o,
   output logic [UID_WIDTH-1:0]                   UID_o,
   input  logic                                   grant_i
);
   logic [$clog2(N_CORES)-1:0]                    arb_FLAG_o;
   genvar j,k;
   generate
      if(N_CORES == 2)
      begin : DUAL_MASTER
          Req_Arb_Node_icache_intc 
          #( 
                  .ADDRESS_WIDTH ( ADDRESS_WIDTH ), 
                  .UID_WIDTH     ( UID_WIDTH     )
          )
          Req_Arb_Node_icache_intc_i
          (
            .request_ch0_i   ( request_i [0] ),
            .address_ch0_i   ( address_i [0] ),
            .UID_ch0_i       ( UID_i     [0] ),
            .grant_ch0_o     ( grant_o   [0] ),

            .request_ch1_i   ( request_i [1] ),
            .address_ch1_i   ( address_i [1] ),    
            .UID_ch1_i       ( UID_i     [1] ),
            .grant_ch1_o     ( grant_o   [1] ),

            .request_o       ( request_o     ),
            .address_o       ( address_o     ),
            .UID_o           ( UID_o         ),
            .grant_i         ( grant_i       ),

            .Flag_i          ( arb_FLAG_o    )
         );
      end 
      else
      begin : MULTI_MASTER
          logic [ADDRESS_WIDTH-1:0]   address_int  [N_CORES-3:0];
          logic                       request_int  [N_CORES-3:0];
          logic [UID_WIDTH-1:0]       UID_int      [N_CORES-3:0];
          logic                       grant_int    [N_CORES-3:0];


            for(j=0; j < $clog2(N_CORES); j++)
            begin : HORIZONTAL_INDEX
              for(k=0; k<2**j; k=k+1)
                begin : VERTICAL_INDEX
                  if (j == 0 )
                  begin : OUT_NODE
                    Req_Arb_Node_icache_intc 
                    #( 
                        .ADDRESS_WIDTH ( ADDRESS_WIDTH ), 
                        .UID_WIDTH     ( UID_WIDTH     )
                    )
                    Req_Arb_Node_icache_intc_i
                    (
                        .request_ch0_i   ( request_int [2*k]                ),
                        .address_ch0_i   ( address_int [2*k]                ),
                        .UID_ch0_i       ( UID_int     [2*k]                ),
                        .grant_ch0_o     ( grant_int   [2*k]                ),

                        .request_ch1_i   ( request_int [2*k+1]              ),
                        .address_ch1_i   ( address_int [2*k+1]              ),    
                        .UID_ch1_i       ( UID_int     [2*k+1]              ),
                        .grant_ch1_o     ( grant_int   [2*k+1]              ),

                        .request_o       ( request_o                        ),
                        .address_o       ( address_o                        ),
                        .UID_o           ( UID_o                            ),
                        .grant_i         ( grant_i                          ),

                        .Flag_i          ( arb_FLAG_o[$clog2(N_CORES)-j-1]  )
                    );
                  end 
                  else if ( j < $clog2(N_CORES) - 1 )
                        begin : INTERNAL_NODES
                          Req_Arb_Node_icache_intc 
                          #( 
                              .ADDRESS_WIDTH ( ADDRESS_WIDTH ), 
                              .UID_WIDTH     ( UID_WIDTH     )
                          )
                          Req_Arb_Node_icache_intc_i 
                          (

                              .request_ch0_i   ( request_int [((2**j)*2-2) + 2*k]    ),
                              .address_ch0_i   ( address_int [((2**j)*2-2) + 2*k]    ),
                              .UID_ch0_i       ( UID_int     [((2**j)*2-2) + 2*k]    ),
                              .grant_ch0_o     ( grant_int   [((2**j)*2-2) + 2*k]    ),

                              .request_ch1_i   ( request_int [((2**j)*2-2) + 2*k+1]  ),
                              .address_ch1_i   ( address_int [((2**j)*2-2) + 2*k+1]  ),    
                              .UID_ch1_i       ( UID_int     [((2**j)*2-2) + 2*k+1]  ),
                              .grant_ch1_o     ( grant_int   [((2**j)*2-2) + 2*k+1]  ),

                              .request_o       ( request_int [((2**(j-1))*2-2) + k]  ),
                              .address_o       ( address_int [((2**(j-1))*2-2) + k]  ),
                              .UID_o           ( UID_int     [((2**(j-1))*2-2) + k]  ),
                              .grant_i         ( grant_int   [((2**(j-1))*2-2) + k]  ),

                              .Flag_i          ( arb_FLAG_o  [$clog2(N_CORES)-j-1]   )   
                          );
                        end 
                     else
                        begin : INPUT_NODES
                             Req_Arb_Node_icache_intc 
                             #( 
                                 .ADDRESS_WIDTH ( ADDRESS_WIDTH ), 
                                 .UID_WIDTH     ( UID_WIDTH     )
                             )
                             Req_Arb_Node_icache_intc_i
                             (
                                 .request_ch0_i   ( request_i   [2*k]                   ),
                                 .address_ch0_i   ( address_i   [2*k]                   ),
                                 .UID_ch0_i       ( UID_i       [2*k]                   ),
                                 .grant_ch0_o     ( grant_o     [2*k]                   ),

                                 .request_ch1_i   ( request_i   [2*k+1]                 ),
                                 .address_ch1_i   ( address_i   [2*k+1]                 ),    
                                 .UID_ch1_i       ( UID_i       [2*k+1]                 ),
                                 .grant_ch1_o     ( grant_o     [2*k+1]                 ),

                                 .request_o       ( request_int [((2**(j-1))*2-2) + k]  ),
                                 .address_o       ( address_int [((2**(j-1))*2-2) + k]  ),
                                 .UID_o           ( UID_int     [((2**(j-1))*2-2) + k]  ),
                                 .grant_i         ( grant_int   [((2**(j-1))*2-2) + k]  ),

                                 .Flag_i          ( arb_FLAG_o[$clog2(N_CORES)-j-1]  )
                             );
                        end
                end

            end

    end
    endgenerate

    // Rotating Priority
    always_ff @(posedge clk_i or negedge rst_ni)
    begin
        if(rst_ni == 1'b0)
           arb_FLAG_o <= '0;
        else
            if( request_o  & grant_i )
            begin
                    arb_FLAG_o <= arb_FLAG_o + 1'b1;
            end
    end

endmodule
