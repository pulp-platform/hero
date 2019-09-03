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
// Module Name:    DistributedArbitrationNetwork_Resp_icache_intc.sv          //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Block linked to processor side, that receives and routes   //
//                 the responses from the memory side- It is Built using      //
//                 2x1 fan_out primitives, with distributed routing and       //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 16/02/2018 : File Created                                  //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module DistributedArbitrationNetwork_Resp_icache_intc #( parameter N_CACHE_BANKS = 16, parameter DATA_WIDTH    = 32 ) 
(
   input logic [N_CACHE_BANKS-1:0]                 response_i,
   input logic [N_CACHE_BANKS-1:0][DATA_WIDTH-1:0] read_data_i,

   output logic                                    response_o,
   output logic [DATA_WIDTH-1:0]                   read_data_o
);
   genvar j,k;
   generate
      
      case(N_CACHE_BANKS)
        1: begin
          assign read_data_o = read_data_i;
          assign response_o  = response_i;
        end //~ single cache banks

        2:       
        begin : DUAL_CACHE_BANKS
           Resp_Arb_Node_icache_intc 
           #(
              .DATA_WIDTH(DATA_WIDTH)
           )
           Resp_Arb_Node_icache_intc_i
           (
              .response_ch0_i  ( response_i    [0] ),
              .read_data_ch0_i ( read_data_i   [0] ),
              .response_ch1_i  ( response_i    [1] ),
              .read_data_ch1_i ( read_data_i   [1] ),
              .response_o      ( response_o        ),
              .read_data_o     ( read_data_o       )
           );
        end //~ 2 cache banks

        default:
        begin : MULTI_CHACHE_BANKS   
              logic                               response_int   [N_CACHE_BANKS-3:0];
              logic [DATA_WIDTH-1:0]              read_data_int  [N_CACHE_BANKS-3:0];
            
                for(j=0; j < $clog2(N_CACHE_BANKS); j++)
                  begin : HORIZ_INCR
                    for(k=0; k<2**j; k=k+1)
                      begin : VERT_INCR
                      
                        if (j == 0 )
                        begin : OUT_NODE
                           Resp_Arb_Node_icache_intc 
                           #(
                              .DATA_WIDTH      ( DATA_WIDTH        )
                           )
                           Resp_Arb_Node_icache_intc_i
                           (
                              .response_ch0_i  ( response_int  [2*k]   ),
                              .read_data_ch0_i ( read_data_int [2*k]   ),
                              .response_ch1_i  ( response_int  [2*k+1] ),
                              .read_data_ch1_i ( read_data_int [2*k+1] ),
                              .response_o      ( response_o            ),
                              .read_data_o     ( read_data_o           )
                           );                        
                        end 
                        else    if ( j < $clog2(N_CACHE_BANKS) - 1)
                                begin : INTERNAL_NODES 
                                   Resp_Arb_Node_icache_intc 
                                   #(
                                      .DATA_WIDTH      ( DATA_WIDTH        )
                                   )
                                   Resp_Arb_Node_icache_intc_i
                                   (
                                      .response_ch0_i  ( response_int  [((2**j)*2-2) + 2*k]    ),
                                      .read_data_ch0_i ( read_data_int [((2**j)*2-2) + 2*k]    ),
                                      .response_ch1_i  ( response_int  [((2**j)*2-2) + 2*k +1] ),
                                      .read_data_ch1_i ( read_data_int [((2**j)*2-2) + 2*k +1] ),
                                      .response_o      ( response_int  [((2**(j-1))*2-2) + k]  ),
                                      .read_data_o     ( read_data_int [((2**(j-1))*2-2) + k]  )
                                   );  
                                end
                                else
                                begin : INPUT_NODES
                                   Resp_Arb_Node_icache_intc 
                                   #(
                                      .DATA_WIDTH      ( DATA_WIDTH        )
                                   )
                                   Resp_Arb_Node_icache_intc_i
                                   (
                                      .response_ch0_i  ( response_i    [2*k]                  ),
                                      .read_data_ch0_i ( read_data_i   [2*k]                  ),
                                      .response_ch1_i  ( response_i    [2*k+1]                ),
                                      .read_data_ch1_i ( read_data_i   [2*k+1]                ),
                                      .response_o      ( response_int  [((2**(j-1))*2-2) + k] ),
                                      .read_data_o     ( read_data_int [((2**(j-1))*2-2) + k] )
                                   );
                                end
                      end
                  end
        end //~default


      endcase // N_CACHE_BANKS




   endgenerate
endmodule
