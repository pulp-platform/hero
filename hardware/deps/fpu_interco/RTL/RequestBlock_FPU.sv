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
// Module Name:    RequestBlock_FPU                                           //
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

module RequestBlock_FPU
#(
    parameter NB_CORES     = 9,
    parameter NB_APU_ARGS  = 2,
    parameter APU_OPCODE_WIDTH = 5,
    parameter ID_WIDTH     = NB_CORES,
    parameter FLAG_WIDTH   = 6,
    parameter DATA_WIDTH   = 32
)
(
    input  logic                                                  clk,
    input  logic                                                  rst_n,


    input  logic [NB_CORES-1:0]                                   data_req_i,
    input  logic [NB_CORES-1:0][NB_APU_ARGS-1:0][DATA_WIDTH-1:0]  data_operands_i,
    input  logic [NB_CORES-1:0][APU_OPCODE_WIDTH-1:0]             data_op_i,
    input  logic [NB_CORES-1:0][ID_WIDTH-1:0]                     data_ID_i,
    input  logic [NB_CORES-1:0][FLAG_WIDTH-1:0]                   data_flag_i,
    output logic [NB_CORES-1:0]                                   data_gnt_o,

    output logic                                                  data_req_o,
    output logic [NB_APU_ARGS-1:0][DATA_WIDTH-1:0]                data_operands_o,
    output logic [APU_OPCODE_WIDTH-1:0]                           data_op_o,
    output logic [ID_WIDTH-1:0]                                   data_ID_o,
    output logic [FLAG_WIDTH-1:0]                                 data_flag_o,
    input  logic                                                  data_gnt_i,


    input   logic                                                 data_r_valid_i,
    input   logic [ID_WIDTH-1:0]                                  data_r_ID_i,

    // GEN VALID_SIGNALS in the response path
    output logic [NB_CORES-1:0]                                   data_r_valid_o
);




    // CHANNEL Power of 2 Expansion
    logic [2**$clog2(NB_CORES)-1:0]                                  data_req_int;
    logic [2**$clog2(NB_CORES)-1:0][NB_APU_ARGS-1:0][DATA_WIDTH-1:0] data_operands_int;
    logic [2**$clog2(NB_CORES)-1:0][APU_OPCODE_WIDTH-1:0]            data_op_int;
    logic [2**$clog2(NB_CORES)-1:0][ID_WIDTH-1:0]                    data_ID_int;
    logic [2**$clog2(NB_CORES)-1:0][FLAG_WIDTH-1:0]                  data_flag_int;
    logic [2**$clog2(NB_CORES)-1:0]                                  data_gnt_int;
    
  

    generate

            if(2**$clog2(NB_CORES) != NB_CORES) // if NB_CORES is not power of 2 --> then use power 2 ports
            begin : _DUMMY_PORTS_
              
              logic [2**$clog2(NB_CORES)-NB_CORES -1 :0]                                  data_req_dummy;
              logic [2**$clog2(NB_CORES)-NB_CORES -1 :0][NB_APU_ARGS-1:0][DATA_WIDTH-1:0] data_operands_dummy;
              logic [2**$clog2(NB_CORES)-NB_CORES -1 :0][APU_OPCODE_WIDTH-1:0]            data_op_dummy;
              logic [2**$clog2(NB_CORES)-NB_CORES -1 :0][ID_WIDTH-1:0]                    data_ID_dummy;
              logic [2**$clog2(NB_CORES)-NB_CORES -1 :0][FLAG_WIDTH-1:0]                  data_flag_dummy;
              logic [2**$clog2(NB_CORES)-NB_CORES -1 :0]                                  data_gnt_dummy;

              assign data_req_dummy        = '0 ;  
              assign data_operands_dummy   = '0 ;   
              assign data_op_dummy         = '0 ;  
              assign data_ID_dummy         = '0 ;
              assign data_flag_dummy       = '0 ;

              assign data_req_int          = { data_req_dummy      , data_req_i      };
              assign data_operands_int     = { data_operands_dummy , data_operands_i };
              assign data_op_int           = { data_op_dummy       , data_op_i       };
              assign data_ID_int           = { data_ID_dummy       , data_ID_i       };
              assign data_flag_int         = { data_flag_dummy     , data_flag_i     };

              for(genvar j=0; j<NB_CORES; j++)
              begin : _MERGING_REAL_AND_DUMMY_PORTS_OUT_          
                 assign data_gnt_o[j]     = data_gnt_int[j];
              end

          end
          else // NB_CORES is power of 2
          begin
            assign data_req_int          = data_req_i;
            assign data_operands_int     = data_operands_i;
            assign data_op_int           = data_op_i;
            assign data_ID_int           = data_ID_i;
            assign data_flag_int         = data_flag_i;
            assign data_gnt_o            = data_gnt_int;
          end


        if(NB_CORES > 1) // Means 2 or more MAster, it requires Arbitration Tree and eires between Arb tree and Test and set interface
        begin : POLY_CH0
            ArbitrationTree_FPU
            #(
                .NB_CORES         ( 2**$clog2(NB_CORES) ),
                .ID_WIDTH         ( ID_WIDTH            ),
                .DATA_WIDTH       ( DATA_WIDTH          ),
                .NB_APU_ARGS      ( NB_APU_ARGS         ),
                .APU_OPCODE_WIDTH ( APU_OPCODE_WIDTH    ),
                .FLAG_WIDTH       ( FLAG_WIDTH          ),
                .MAX_COUNT        ( NB_CORES            )
            ) 
            i_ArbitrationTree_FPU
            (
                .clk             ( clk               ),
                .rst_n           ( rst_n             ),
                // INPUTS
                .data_req_i      ( data_req_int      ),
                .data_operands_i ( data_operands_int ),
                .data_op_i       ( data_op_int       ),
                .data_ID_i       ( data_ID_int       ),
                .data_flag_i     ( data_flag_int     ),
                .data_gnt_o      ( data_gnt_int      ),
                // OUTPUTS
                .data_req_o      ( data_req_o        ),
                .data_operands_o ( data_operands_o   ),
                .data_op_o       ( data_op_o         ),
                .data_ID_o       ( data_ID_o         ),
                .data_flag_o     ( data_flag_o       ),
                .data_gnt_i      ( data_gnt_i        )
            );
        end
        else
        begin : MONO_CH0
          assign data_req_o       = data_req_int;
          assign data_operands_o  = data_operands_int;
          assign data_op_o        = data_op_int;
          assign data_ID_o        = data_ID_int;
          assign data_flag_o      = data_gnt_int;
          assign data_gnt_int     = data_gnt_i;
        end

    endgenerate

    AddressDecoder_Resp_FPU 
    #( 
        .ID_WIDTH(ID_WIDTH), 
        .NB_CORES(NB_CORES)
    ) 
    i_AddressDecoder_Resp_FPU
    (
      // FROM Test And Set Interface
      .data_r_valid_i ( data_r_valid_i  ),
      .data_ID_i      ( data_r_ID_i     ),
      // To Response Network
      .data_r_valid_o ( data_r_valid_o  )
    );



endmodule
