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
// Module Name:    XBAR_FPU                                                   //
// Project Name:   VEGA                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Top for the FPU interco, which instantiate response and    //
//                 request blocks, and eventually the Optimal allocator.      //
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

module XBAR_FPU 
#(
    parameter NB_CORES         = 2,
    parameter NB_APUS          = 1,
    parameter NB_APU_ARGS      = 3,
    parameter APU_DATA_WIDTH   = 64,
    parameter APU_OPCODE_WIDTH = 5,
    parameter APU_DSFLAGS_CPU  = 15,
    parameter APU_USFLAGS_CPU  = 5,
    parameter ID_WIDTH         = NB_CORES,

    parameter int unsigned  LFSR_SEED    = 7,

    parameter USE_OPT_ALLOC              = "TRUE" // Valid Choices are --> "TRUE" | "FALSE"
)
(
    input  logic                                                        clk,
    input  logic                                                        rst_n,

    // CORE SIDE: Slave port
    input  logic [NB_CORES-1:0]                                         apu_slave_req_i,
    output logic [NB_CORES-1:0]                                         apu_slave_gnt_o,

    // request channel
    input logic [NB_CORES-1:0][NB_APU_ARGS-1:0][APU_DATA_WIDTH-1:0]     apu_slave_operands_i,
    input logic [NB_CORES-1:0][APU_OPCODE_WIDTH-1:0]                    apu_slave_op_i,
    input logic [NB_CORES-1:0][APU_DSFLAGS_CPU-1:0]                     apu_slave_flags_i,


    // response channel
    output logic [NB_CORES-1:0]                                         apu_slave_rvalid_o,
    input  logic [NB_CORES-1:0]                                         apu_slave_ready_i, // not used
    output logic [NB_CORES-1:0][APU_DATA_WIDTH-1:0]                     apu_slave_rdata_o,
    output logic [NB_CORES-1:0][APU_USFLAGS_CPU-1:0]                    apu_slave_rflags_o,


    // APU Side: Master port
    output logic [NB_APUS-1:0]                                          apu_master_req_o,
    input  logic [NB_APUS-1:0]                                          apu_master_gnt_i,
    output logic [NB_APUS-1:0][ID_WIDTH-1:0]                            apu_master_ID_o,

    // request channel
    output logic [NB_APUS-1:0][NB_APU_ARGS-1:0][APU_DATA_WIDTH-1:0]     apu_master_operands_o,
    output logic [NB_APUS-1:0][APU_OPCODE_WIDTH-1:0]                    apu_master_op_o,
    output logic [NB_APUS-1:0][APU_DSFLAGS_CPU-1:0]                     apu_master_flags_o,

    // response channel
    output logic [NB_APUS-1:0]                                          apu_master_ready_o, // not used
    input  logic [NB_APUS-1:0]                                          apu_master_rvalid_i,
    input  logic [NB_APUS-1:0][APU_DATA_WIDTH-1:0]                      apu_master_rdata_i,
    input  logic [NB_APUS-1:0][APU_USFLAGS_CPU-1:0]                     apu_master_rflags_i,
    input  logic [NB_APUS-1:0][ID_WIDTH-1:0]                            apu_master_rID_i  
);

    // DATA ID array FROM address decoders to Request tree.
    logic [NB_CORES-1:0][ID_WIDTH-1:0]              data_ID;

    logic [NB_CORES-1:0]                            fpu_gnt_from_APU[NB_APUS-1:0];
    logic [NB_APUS-1:0]                             fpu_req_from_CORE[NB_CORES-1:0];

    logic [NB_APUS-1:0][NB_CORES-1:0]               fpu_r_valid_from_APU;
    logic [NB_CORES-1:0][NB_APUS-1:0]               fpu_r_valid_to_CORE;
    
    logic [NB_CORES-1:0]                            fpu_req_to_APU[NB_APUS-1:0];
    logic [NB_APUS-1:0]                             fpu_gnt_to_CORE[NB_CORES-1:0];

    logic [NB_CORES-1:0][$clog2(NB_APUS)-1:0]       ROUTING_ADDR;

    genvar j,k;

    assign apu_master_ready_o   = '1;

    generate

        for (k=0; k<NB_CORES; k++)
        begin : BINDING_X_WIRES_CORE_FPU_FC

          for (j=0; j<NB_APUS; j++)
            begin : APU
              assign fpu_r_valid_to_CORE[k][j] = fpu_r_valid_from_APU[j][k];
              assign fpu_req_to_APU[j][k]      = fpu_req_from_CORE[k][j];
              assign fpu_gnt_to_CORE[k][j]     = fpu_gnt_from_APU[j][k];
            end

        end



        for (j=0; j<  NB_APUS; j++)
        begin : FPURequestBlock

              RequestBlock_FPU  
              #( 
                  .NB_CORES         ( NB_CORES           ),
                  .NB_APU_ARGS      ( NB_APU_ARGS        ),
                  .APU_OPCODE_WIDTH ( APU_OPCODE_WIDTH   ),
                  .ID_WIDTH         ( ID_WIDTH           ),
                  .FLAG_WIDTH       ( APU_DSFLAGS_CPU    ),
                  .DATA_WIDTH       ( APU_DATA_WIDTH     )
              ) 
              i_RequestBlock_FPU
              (
                .data_req_i      ( fpu_req_to_APU[j]    ),
                .data_operands_i ( apu_slave_operands_i ),
                .data_op_i       ( apu_slave_op_i       ),
                .data_ID_i       ( data_ID              ),
                .data_flag_i     ( apu_slave_flags_i    ),
                .data_gnt_o      ( fpu_gnt_from_APU[j]  ),

                // -----------------             APU                    -------------------
                // ---------------- RequestBlock OUTPUT (Connected to APUORY) ----------------
                .data_req_o      ( apu_master_req_o[j]       ),
                .data_operands_o ( apu_master_operands_o[j]  ),
                .data_op_o       ( apu_master_op_o[j]        ),
                .data_ID_o       ( apu_master_ID_o[j]        ),
                .data_flag_o     ( apu_master_flags_o[j]     ),
                .data_gnt_i      ( apu_master_gnt_i[j]       ),

                .data_r_valid_i  ( apu_master_rvalid_i[j]    ),
                .data_r_ID_i     ( apu_master_rID_i[j]       ),

                // GEN VALID_SIGNALS in the response path
                .data_r_valid_o  ( fpu_r_valid_from_APU[j]   ), 
                
                .clk             ( clk                       ),
                .rst_n           ( rst_n                     )
            );
        end



        for (j=0; j<  NB_CORES; j++)
        begin : ResponseBlock_FPU_Block

            ResponseBlock_FPU 
            #( 
                .DATA_WIDTH     ( APU_DATA_WIDTH        ),
                .ID_WIDTH       ( ID_WIDTH              ), 
                .NB_APUS        ( NB_APUS               ),
                .RFLAG_WIDTH    ( APU_USFLAGS_CPU       ),
                .ID             ( 2**j                  ), 
                .LFSR_SEED      ( LFSR_SEED             ),
                .USE_OPT_ALLOC  ( USE_OPT_ALLOC         )
            ) 
            i_ResponseBlock_FPU
            (
                .clk            ( clk                   ),
                .rst_n          ( rst_n                 ),
                
                .data_r_valid_i ( fpu_r_valid_to_CORE[j] ),
                .data_r_rdata_i ( apu_master_rdata_i     ),
                .data_r_flag_i  ( apu_master_rflags_i    ),

                // Output of the ResponseTree Block
                .data_r_valid_o ( apu_slave_rvalid_o[j]  ),
                .data_r_rdata_o ( apu_slave_rdata_o[j]   ),
                .data_r_flag_o  ( apu_slave_rflags_o[j]  ),
                
                // Inputs form CORES
                .apu_status_i   ( apu_master_req_o       ),
                .data_req_i     ( apu_slave_req_i[j]     ),
                .data_gnt_o     ( apu_slave_gnt_o[j]     ),  // grant to master port
                .ROUTING_ADDR_i ( ROUTING_ADDR[j]        ),

                .data_gnt_i     ( fpu_gnt_to_CORE[j]     ), // Signal from Request Block
                .data_req_o     ( fpu_req_from_CORE[j]   ),

                // Generated ID
                .data_ID_o      ( data_ID[j]             )
            );
          end

          if(USE_OPT_ALLOC == "TRUE")
          begin : OPT_ALLOC
                optimal_alloc
                #(
                    .NB_CORES       ( NB_CORES ),
                    .NB_APUS        ( NB_APUS  )
                )
                RoutingAddr_Gen
                (
                    .req_i          ( apu_slave_req_i ),
                    .ROUTING_ADDR_o ( ROUTING_ADDR    )
                );
          end
          else
          begin
                assign ROUTING_ADDR  = '0;
          end

    endgenerate


endmodule
