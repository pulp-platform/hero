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
// Module Name:    ResponseBlock_FPU                                          //
// Project Name:   VEGA                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    This block is used to collect all the response from        //
//                 different fpnew, and to multiplex thrm to the core port.   //
//                 It also include the Second stage allocator to point the    //
//                 rigth allocator and ID generation for backrouting          //
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

module ResponseBlock_FPU
#(
    parameter ID_WIDTH       = 9,
    parameter NB_APUS        = 1,
    parameter DATA_WIDTH     = 32,
    parameter RFLAG_WIDTH    = 6,
    parameter USE_OPT_ALLOC  = "TRUE",

    parameter int unsigned  ID           = 1,
    parameter int unsigned  LFSR_SEED    = 7
)
(
        input logic                                     clk,
        input logic                                     rst_n, 

        // Signals from Memory cuts
        input logic [NB_APUS-1:0]                       data_r_valid_i,
        input logic [NB_APUS-1:0][DATA_WIDTH-1:0]       data_r_rdata_i,
        input logic [NB_APUS-1:0][RFLAG_WIDTH-1:0]      data_r_flag_i,
        
        // Output of the ResponseTree Block
        output logic                                    data_r_valid_o,
        output logic [DATA_WIDTH-1:0]                   data_r_rdata_o,
        output logic [RFLAG_WIDTH-1:0]                  data_r_flag_o,



        // -----------------------------------------------------------//
        //                      Request HANDLING
        // -----------------------------------------------------------//
        input logic                                     data_req_i,
        input logic [NB_APUS-1:0]                       apu_status_i,
        output logic                                    data_gnt_o,  
        input  logic [$clog2(NB_APUS)-1:0]              ROUTING_ADDR_i,        

        
        output logic [NB_APUS-1:0]                       data_req_o,
        input  logic [NB_APUS-1:0]                       data_gnt_i,
        output logic [ID_WIDTH-1:0]                      data_ID_o
);
        




    genvar i;




    generate
        if(NB_APUS==1)
        begin : MONO_APU
             assign  data_r_valid_o  = data_r_valid_i[0];
             assign  data_r_rdata_o  = data_r_rdata_i[0];
             assign  data_r_flag_o   = data_r_flag_i[0];
        end
        else 
        begin : MULTI_APU

                    // Response channel exploded to powr of 2 inputs
                    logic [2**$clog2(NB_APUS)-1:0]                     data_r_valid_int;
                    logic [2**$clog2(NB_APUS)-1:0][DATA_WIDTH-1:0]     data_r_rdata_int;
                    logic [2**$clog2(NB_APUS)-1:0][RFLAG_WIDTH-1:0]    data_r_flag_int;


                    if(2**$clog2(NB_APUS) == NB_APUS)
                    begin : EXACT_POW2

                      for(i=0;i<NB_APUS;i++)
                      begin
                        assign data_r_valid_int[i] = data_r_valid_i[i];
                        assign data_r_rdata_int[i] = data_r_rdata_i[i];
                        assign data_r_flag_int[i]  = data_r_flag_i[i];
                      end


                    end
                    else
                    begin : NOT_POW2
                      for(i=0; i<2**$clog2(NB_APUS); i++)
                      begin
                          if(i<NB_APUS)
                          begin
                            assign data_r_valid_int[i] = data_r_valid_i[i];
                            assign data_r_rdata_int[i] = data_r_rdata_i[i];
                            assign data_r_flag_int[i]  = data_r_flag_i[i];
                          end
                          else
                          begin
                            assign data_r_valid_int[i] = 1'b0;
                            assign data_r_rdata_int[i] = '0;
                            assign data_r_flag_int[i]  = '0;
                          end                    
                      end
                    end

                    // Response Tree
                    ResponseTree_FPU
                    #( 
                        .NB_APUS    ( 2**$clog2(NB_APUS) ), 
                        .FLAG_WIDTH ( RFLAG_WIDTH        ),
                        .DATA_WIDTH ( DATA_WIDTH         )
                    )
                    i_ResponseTree_FPU
                    (
                          // Response Input Channel
                          .data_r_valid_i ( data_r_valid_int ),
                          .data_r_rdata_i ( data_r_rdata_int ),
                          .data_r_flag_i  ( data_r_flag_int  ),
                          // Response Output Channel
                          .data_r_valid_o ( data_r_valid_o   ),
                          .data_r_rdata_o ( data_r_rdata_o   ),
                          .data_r_flag_o  ( data_r_flag_o    )
                    );

        end


    endgenerate

      AddressDecoder_Req_FPU
      #( 
         .ID_WIDTH       ( ID_WIDTH        ), 
         .ID             ( ID              ), 
         .NB_APUS        ( NB_APUS         ),
         .SEED           ( LFSR_SEED       ),
         .USE_OPT_ALLOC  ( USE_OPT_ALLOC   )      
      )
      i_AddressDecoder_FPU_Req
      (
        .clk            ( clk            ),
        .rst_n          ( rst_n          ),
        // MASTER SIDE
        .data_req_i     ( data_req_i     ),
        .ROUTING_ADDR_i ( ROUTING_ADDR_i ),
        .apu_status_i   ( apu_status_i   ),
        .data_gnt_o     ( data_gnt_o     ),
        .data_gnt_i     ( data_gnt_i     ),
        // ARB TREE SIDE
        .data_req_o     ( data_req_o     ),
        .data_ID_o      ( data_ID_o      )
      );


endmodule
