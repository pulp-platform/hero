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
// Module Name:    ResponseTree_FPU                                           //
// Project Name:   VEGA                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:                                                               //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 01/01/2019 : File Created                                  //
//                                                                            //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module ResponseTree_FPU
#(
   parameter NB_APUS     = 16,
   parameter FLAG_WIDTH  = 8,
   parameter DATA_WIDTH  = 32
) 
(
   // Response Input Channel 0
   input logic [NB_APUS-1:0]                    data_r_valid_i,
   input logic [NB_APUS-1:0][DATA_WIDTH-1:0]    data_r_rdata_i,
   input logic [NB_APUS-1:0][FLAG_WIDTH-1:0]    data_r_flag_i,
   // Response Output Channel
   output logic                                 data_r_valid_o,
   output logic [DATA_WIDTH-1:0]                data_r_rdata_o,
   output logic [FLAG_WIDTH-1:0]                data_r_flag_o
);

   localparam LOG_NB_APUS       = $clog2(NB_APUS);
   localparam N_WIRE           =  NB_APUS - 2;

   genvar j,k;

   generate

      if(NB_APUS == 2)
      begin : INCR // START of  NB_APUS  == 2
         // ---------------- FAN IN PRIMITIVE RESP -------------------------
         FanInPrimitive_Resp_FPU 
         #(
            .FLAG_WIDTH ( FLAG_WIDTH ),
            .DATA_WIDTH ( DATA_WIDTH )
         )
         i_FanInPrimitive_Resp_FPU
         (
            // RIGTH SIDE
            .data_r_rdata0_i ( data_r_rdata_i[0] ),
            .data_r_rdata1_i ( data_r_rdata_i[1] ),
            .data_r_valid0_i ( data_r_valid_i[0] ),
            .data_r_valid1_i ( data_r_valid_i[1] ),
            .data_r_flag0_i  ( data_r_flag_i [0] ),
            .data_r_flag1_i  ( data_r_flag_i [1] ),
            // LEFT SIDE
            .data_r_rdata_o  ( data_r_rdata_o    ),
            .data_r_valid_o  ( data_r_valid_o    ),
            .data_r_flag_o   ( data_r_flag_o     )
         );
      end // END OF NB_APUS  == 2
      else // More than two master
      begin : BINARY_TREE
            //// ---------------------------------------------------------------------- ////
            //// -------               REQ ARBITRATION TREE WIRES           ----------- ////
            //// ---------------------------------------------------------------------- ////    
            logic [N_WIRE-1:0][DATA_WIDTH-1:0]              data_r_rdata_LEVEL;
            logic [N_WIRE-1:0]                              data_r_valid_LEVEL;
            logic [N_WIRE-1:0][FLAG_WIDTH-1:0]              data_r_flag_LEVEL;
          
              for(j=0; j < LOG_NB_APUS; j++) // Iteration for the number of the stages minus one
                begin : STAGE
                  for(k=0; k<2**j; k=k+1) // Iteration needed to create the binary tree
                    begin : INCR_VERT
                    
                      if (j == 0 )  // LAST NODE, drives the module outputs
                      begin : LAST_NODE
                          FanInPrimitive_Resp_FPU 
                          #(
                              .FLAG_WIDTH ( FLAG_WIDTH ),
                              .DATA_WIDTH ( DATA_WIDTH )
                          )
                          i_FanInPrimitive_Resp_FPU
                          (
                             // RIGTH SIDE
                             .data_r_rdata0_i ( data_r_rdata_LEVEL [2*k]    ),
                             .data_r_rdata1_i ( data_r_rdata_LEVEL [2*k+1]  ),
                             .data_r_valid0_i ( data_r_valid_LEVEL [2*k]    ),
                             .data_r_valid1_i ( data_r_valid_LEVEL [2*k+1]  ),
                             .data_r_flag0_i  ( data_r_flag_LEVEL  [2*k]    ),
                             .data_r_flag1_i  ( data_r_flag_LEVEL  [2*k+1]  ),
                             // RIGTH SIDE
                             .data_r_rdata_o  ( data_r_rdata_o              ),
                             .data_r_valid_o  ( data_r_valid_o              ),
                             .data_r_flag_o   ( data_r_flag_o               )
                          );
                      end 
                      else if ( j < LOG_NB_APUS - 1) // Middle Nodes
                              begin : MIDDLE_NODES // START of MIDDLE LEVELS Nodes   
                                  FanInPrimitive_Resp_FPU 
                                  #(
                                      .FLAG_WIDTH ( FLAG_WIDTH ),
                                      .DATA_WIDTH ( DATA_WIDTH )
                                  )
                                  i_FanInPrimitive_Resp_FPU
                                  (
                                     // RIGTH SIDE                           
                                     .data_r_rdata0_i ( data_r_rdata_LEVEL [((2**j)*2-2) + 2*k]    ),
                                     .data_r_rdata1_i ( data_r_rdata_LEVEL [((2**j)*2-2) + 2*k+1]  ),
                                     .data_r_valid0_i ( data_r_valid_LEVEL [((2**j)*2-2) + 2*k]    ),
                                     .data_r_valid1_i ( data_r_valid_LEVEL [((2**j)*2-2) + 2*k+1]  ),
                                     .data_r_flag0_i  ( data_r_flag_LEVEL  [((2**j)*2-2) + 2*k]    ),
                                     .data_r_flag1_i  ( data_r_flag_LEVEL  [((2**j)*2-2) + 2*k+1]  ),                                                         
                                     // LEFT SIDE
                                     .data_r_rdata_o  ( data_r_rdata_LEVEL [((2**(j-1))*2-2) + k]  ),
                                     .data_r_valid_o  ( data_r_valid_LEVEL [((2**(j-1))*2-2) + k]  ),
                                     .data_r_flag_o   ( data_r_flag_LEVEL  [((2**(j-1))*2-2) + k]  )
                                  );
                              end  // END of MIDDLE LEVELS Nodes   
                           else // First stage (connected with the Main inputs ) --> ( j == NB_APUS - 1 )
                              begin : LEAF_NODES  // START of FIRST LEVEL Nodes (LEAF)
                                  FanInPrimitive_Resp_FPU 
                                  #(
                                      .FLAG_WIDTH ( FLAG_WIDTH ),
                                      .DATA_WIDTH ( DATA_WIDTH )
                                  )
                                  i_FanInPrimitive_Resp_FPU
                                  (
                                     // RIGTH SIDE 
                                     .data_r_rdata0_i ( data_r_rdata_i [2*k]                       ),
                                     .data_r_rdata1_i ( data_r_rdata_i [2*k+1]                     ),
                                     .data_r_valid0_i ( data_r_valid_i [2*k]                       ),
                                     .data_r_valid1_i ( data_r_valid_i [2*k+1]                     ),
                                     .data_r_flag0_i  ( data_r_flag_i  [2*k]                       ),
                                     .data_r_flag1_i  ( data_r_flag_i  [2*k+1]                     ),  
                                     // LEFT SIDE
                                     .data_r_rdata_o  ( data_r_rdata_LEVEL [((2**(j-1))*2-2) + k]  ),
                                     .data_r_valid_o  ( data_r_valid_LEVEL [((2**(j-1))*2-2) + k]  ),
                                     .data_r_flag_o   ( data_r_flag_LEVEL  [((2**(j-1))*2-2) + k]  )
                                  );
                              end // End of FIRST LEVEL Nodes (LEAF)
                    end
                  
                end
   end
   endgenerate


endmodule
