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
// Module Name:    AddressDecoder_Resp_FPU                                    //
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


module ArbitrationTree_FPU
#(
    parameter DATA_WIDTH       = 32,
    parameter NB_CORES         = 9,
    parameter ID_WIDTH         = NB_CORES,
    parameter NB_APU_ARGS      = 3,
    parameter APU_OPCODE_WIDTH = 6,
    parameter FLAG_WIDTH       = 8,
    parameter MAX_COUNT        = NB_CORES
) 
(
    input  logic                                                 clk,
    input  logic                                                 rst_n,

    // ---------------- REQ_SIDE --------------------------
    input  logic [NB_CORES-1:0]                                  data_req_i,
    input  logic [NB_CORES-1:0][NB_APU_ARGS-1:0][DATA_WIDTH-1:0] data_operands_i,
    input  logic [NB_CORES-1:0][APU_OPCODE_WIDTH-1:0]            data_op_i,
    input  logic [NB_CORES-1:0][ID_WIDTH-1:0]                    data_ID_i,
    input  logic [NB_CORES-1:0][FLAG_WIDTH-1:0]                  data_flag_i,
    output logic [NB_CORES-1:0]                                  data_gnt_o,


    // Outputs
    output logic                                                 data_req_o,
    output logic [NB_APU_ARGS-1:0][DATA_WIDTH-1:0]               data_operands_o,
    output logic [APU_OPCODE_WIDTH-1:0]                          data_op_o,
    output logic [ID_WIDTH-1:0]                                  data_ID_o,
    output logic [FLAG_WIDTH-1:0]                                data_flag_o,    
    input  logic                                                 data_gnt_i
);

    localparam LOG_NB_CORES     = $clog2(NB_CORES);
    localparam N_WIRE           =  NB_CORES - 2;

    logic [LOG_NB_CORES-1:0]      RR_FLAG;

    genvar j,k;

    generate
      if(NB_CORES == 2)
      begin : INCR // START of  MASTER  == 2
                // ---------------- FAN IN PRIMITIVE  -------------------------
                FanInPrimitive_Req_FPU
                #(
                   .NB_APU_ARGS      ( NB_APU_ARGS      ),
                   .APU_OPCODE_WIDTH ( APU_OPCODE_WIDTH ),
                   .ID_WIDTH         ( ID_WIDTH         ),
                   .DATA_WIDTH       ( DATA_WIDTH       ),
                   .FLAG_WIDTH       ( FLAG_WIDTH       )
                )
                i_FanInPrimitive_Req_FPU
                (
                  .RR_FLAG         ( RR_FLAG            ),
                  // UPSTREAM SIDE
                  .data_operand0_i ( data_operands_i[0] ),
                  .data_operand1_i ( data_operands_i[1] ),
                  .data_op0_i      ( data_op_i      [0] ),
                  .data_op1_i      ( data_op_i      [1] ),    
                  .data_req0_i     ( data_req_i     [0] ),
                  .data_req1_i     ( data_req_i     [1] ),
                  .data_ID0_i      ( data_ID_i      [0] ),
                  .data_ID1_i      ( data_ID_i      [1] ),
                  .data_flag0_i    ( data_flag_i    [0] ),
                  .data_flag1_i    ( data_flag_i    [1] ),
                  .data_gnt0_o     ( data_gnt_o     [0] ),
                  .data_gnt1_o     ( data_gnt_o     [1] ),

                  // DOWNSTREAM SIDE
                  .data_operand_o  ( data_operands_o    ),
                  .data_op_o       ( data_op_o          ),
                  .data_req_o      ( data_req_o         ),
                  .data_ID_o       ( data_ID_o          ),
                  .data_flag_o     ( data_flag_o        ),
                  .data_gnt_i      ( data_gnt_i         )
                );
      end // END OF NB_CORES  == 2
      else // More than two master
      begin : BINARY_TREE
          //// ---------------------------------------------------------------------- ////
          //// -------               REQ ARBITRATION TREE WIRES           ----------- ////
          //// ---------------------------------------------------------------------- ////      
          logic [N_WIRE-1:0][NB_APU_ARGS-1:0][DATA_WIDTH-1:0]  data_operands_LEVEL;
          logic [N_WIRE-1:0][APU_OPCODE_WIDTH-1:0]             data_op_LEVEL;
          logic [N_WIRE-1:0][FLAG_WIDTH-1:0]                   data_flag_LEVEL;
          logic [N_WIRE-1:0]                                   data_req_LEVEL;
          logic [N_WIRE-1:0][ID_WIDTH-1:0]                     data_ID_LEVEL;
          logic [N_WIRE-1:0]                                   data_gnt_LEVEL;


            for(j=0; j < LOG_NB_CORES; j++) // Iteration for the number of the stages minus one
            begin : STAGE
              for(k=0; k<2**j; k=k+1) // Iteration needed to create the binary tree
                begin : INCR_VERT
                  if (j == 0 )  // LAST NODE, drives the module outputs
                  begin : LAST_NODE
                    FanInPrimitive_Req_FPU
                    #( 
                       .DATA_WIDTH       ( DATA_WIDTH       ),
                       .NB_APU_ARGS      ( NB_APU_ARGS      ),
                       .APU_OPCODE_WIDTH ( APU_OPCODE_WIDTH ),
                       .ID_WIDTH         ( ID_WIDTH         ),
                       .FLAG_WIDTH       ( FLAG_WIDTH       )
                    )
                    i_FanInPrimitive_Req_FPU
                    (
                        .RR_FLAG       ( RR_FLAG[LOG_NB_CORES-j-1] ),
                        // UPSTREAM SIDE
                        .data_operand0_i ( data_operands_LEVEL[2*k]   ),
                        .data_operand1_i ( data_operands_LEVEL[2*k+1] ),
                        .data_op0_i      ( data_op_LEVEL      [2*k]   ),
                        .data_op1_i      ( data_op_LEVEL      [2*k+1] ), 
                        .data_req0_i     ( data_req_LEVEL     [2*k]   ),
                        .data_req1_i     ( data_req_LEVEL     [2*k+1] ),
                        .data_ID0_i      ( data_ID_LEVEL      [2*k]   ),
                        .data_ID1_i      ( data_ID_LEVEL      [2*k+1] ),
                        .data_flag0_i    ( data_flag_LEVEL    [2*k]   ),
                        .data_flag1_i    ( data_flag_LEVEL    [2*k+1] ),                        
                        .data_gnt0_o     ( data_gnt_LEVEL     [2*k]   ),
                        .data_gnt1_o     ( data_gnt_LEVEL     [2*k+1] ),
                        // DOWNSTREAM SIDE
                        .data_operand_o  ( data_operands_o        ),
                        .data_op_o       ( data_op_o              ),
                        .data_req_o      ( data_req_o             ),
                        .data_ID_o       ( data_ID_o              ),
                        .data_flag_o     ( data_flag_o            ),
                        .data_gnt_i      ( data_gnt_i             )
                    );
                  end 
                  else if ( j < LOG_NB_CORES - 1) // Middle Nodes
                        begin : MIDDLE_NODES // START of MIDDLE LEVELS Nodes   
                          FanInPrimitive_Req_FPU
                          #( 
                               .DATA_WIDTH       ( DATA_WIDTH       ),
                               .NB_APU_ARGS      ( NB_APU_ARGS      ),
                               .APU_OPCODE_WIDTH ( APU_OPCODE_WIDTH ),
                               .ID_WIDTH         ( ID_WIDTH         ),
                               .FLAG_WIDTH       ( FLAG_WIDTH       )
                          )
                          i_FanInPrimitive_Req_FPU
                          (
                              .RR_FLAG(RR_FLAG[LOG_NB_CORES-j-1]),
                              // LEFT SIDE
                              .data_operand0_i ( data_operands_LEVEL [((2**j)*2-2) + 2*k]     ),
                              .data_operand1_i ( data_operands_LEVEL [((2**j)*2-2) + 2*k +1]  ),
                              .data_op0_i      ( data_op_LEVEL       [((2**j)*2-2) + 2*k]     ),
                              .data_op1_i      ( data_op_LEVEL       [((2**j)*2-2) + 2*k+1]   ),
                              .data_req0_i     ( data_req_LEVEL      [((2**j)*2-2) + 2*k]     ),
                              .data_req1_i     ( data_req_LEVEL      [((2**j)*2-2) + 2*k+1]   ),
                              .data_ID0_i      ( data_ID_LEVEL       [((2**j)*2-2) + 2*k]     ),
                              .data_ID1_i      ( data_ID_LEVEL       [((2**j)*2-2) + 2*k+1]   ),
                              .data_flag0_i    ( data_flag_LEVEL     [((2**j)*2-2) + 2*k]     ),
                              .data_flag1_i    ( data_flag_LEVEL     [((2**j)*2-2) + 2*k+1]   ),
                              .data_gnt0_o     ( data_gnt_LEVEL      [((2**j)*2-2) + 2*k]     ),
                              .data_gnt1_o     ( data_gnt_LEVEL      [((2**j)*2-2) + 2*k+1]   ),

                              // RIGTH SIDE
                              .data_operand_o  ( data_operands_LEVEL [((2**(j-1))*2-2) + k]   ),
                              .data_op_o       ( data_op_LEVEL       [((2**(j-1))*2-2) + k]   ),
                              .data_req_o      ( data_req_LEVEL      [((2**(j-1))*2-2) + k]   ),
                              .data_ID_o       ( data_ID_LEVEL       [((2**(j-1))*2-2) + k]   ),
                              .data_flag_o     ( data_flag_LEVEL     [((2**(j-1))*2-2) + k]   ),
                              .data_gnt_i      ( data_gnt_LEVEL      [((2**(j-1))*2-2) + k]   )
                          );
                        end  // END of MIDDLE LEVELS Nodes   
                     else // First stage (connected with the Main inputs ) --> ( j == N_MASTER - 1 )
                        begin : LEAF_NODES  // START of FIRST LEVEL Nodes (LEAF)
                            FanInPrimitive_Req_FPU 
                            #( 
                               .DATA_WIDTH       ( DATA_WIDTH       ),
                               .NB_APU_ARGS      ( NB_APU_ARGS      ),
                               .APU_OPCODE_WIDTH ( APU_OPCODE_WIDTH ),
                               .ID_WIDTH         ( ID_WIDTH         ),
                               .FLAG_WIDTH       ( FLAG_WIDTH       )
                            )
                            i_FanInPrimitive_Req_FPU
                            (
                                .RR_FLAG(RR_FLAG[LOG_NB_CORES-j-1]),
                                // LEFT SIDE
                                .data_operand0_i ( data_operands_i [2*k]   ),
                                .data_operand1_i ( data_operands_i [2*k+1] ),
                                .data_op0_i      ( data_op_i       [2*k]   ),
                                .data_op1_i      ( data_op_i       [2*k+1] ),
                                .data_req0_i     ( data_req_i      [2*k]   ),
                                .data_req1_i     ( data_req_i      [2*k+1] ),
                                .data_ID0_i      ( data_ID_i       [2*k]   ),
                                .data_ID1_i      ( data_ID_i       [2*k+1] ),
                                .data_flag0_i    ( data_flag_i     [2*k]   ),
                                .data_flag1_i    ( data_flag_i     [2*k+1] ),
                                .data_gnt0_o     ( data_gnt_o      [2*k]   ),
                                .data_gnt1_o     ( data_gnt_o      [2*k+1] ),
  
                                // RIGTH SIDE
                                .data_operand_o  ( data_operands_LEVEL [((2**(j-1))*2-2) + k]   ),
                                .data_op_o       ( data_op_LEVEL       [((2**(j-1))*2-2) + k]   ),
                                .data_req_o      ( data_req_LEVEL      [((2**(j-1))*2-2) + k]   ),
                                .data_ID_o       ( data_ID_LEVEL       [((2**(j-1))*2-2) + k]   ),
                                .data_flag_o     ( data_flag_LEVEL     [((2**(j-1))*2-2) + k]   ),
                                .data_gnt_i      ( data_gnt_LEVEL      [((2**(j-1))*2-2) + k]   )
                            );
                        end // End of FIRST LEVEL Nodes (LEAF)
                end

            end

    end
    endgenerate

    //COUNTER USED TO SWITCH PERIODICALLY THE PRIORITY FLAG"
    RR_Flag_Req_FPU
    #( 
        .WIDTH     ( LOG_NB_CORES),
        .MAX_COUNT ( MAX_COUNT)
    )  
    RR_REQ
    (
      .clk          ( clk          ),
      .rst_n        ( rst_n        ),
      .RR_FLAG_o    ( RR_FLAG      ),
      .data_req_i   ( data_req_o   ),
      .data_gnt_i   ( data_gnt_i   )
    );


endmodule
