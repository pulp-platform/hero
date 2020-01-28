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
// Module Name:    FanInPrimitive_Req_FPU                                     //
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



module FanInPrimitive_Req_FPU
#(
    parameter DATA_WIDTH       = 32,
    parameter NB_APU_ARGS      = 2,
    parameter APU_OPCODE_WIDTH = 6,
    parameter ID_WIDTH         = 9,
    parameter FLAG_WIDTH       = 9
)
(
    input logic                                    RR_FLAG,
    input logic  [NB_APU_ARGS-1:0][DATA_WIDTH-1:0] data_operand0_i,
    input logic  [NB_APU_ARGS-1:0][DATA_WIDTH-1:0] data_operand1_i,
    input logic  [APU_OPCODE_WIDTH-1:0]            data_op0_i,
    input logic  [APU_OPCODE_WIDTH-1:0]            data_op1_i,
    input logic                                    data_req0_i,
    input logic                                    data_req1_i,
    input logic  [ID_WIDTH-1:0]                    data_ID0_i,
    input logic  [ID_WIDTH-1:0]                    data_ID1_i,
    input logic  [FLAG_WIDTH-1:0]                  data_flag0_i,
    input logic  [FLAG_WIDTH-1:0]                  data_flag1_i,
    output logic                                   data_gnt0_o,
    output logic                                   data_gnt1_o,

    // RIGTH SIDE
    output logic [NB_APU_ARGS-1:0][DATA_WIDTH-1:0] data_operand_o,
    output logic [APU_OPCODE_WIDTH-1:0]            data_op_o,
    output logic                                   data_req_o,
    output logic [ID_WIDTH-1:0]                    data_ID_o,
    output logic [FLAG_WIDTH-1:0]                  data_flag_o,
    input  logic                                   data_gnt_i
);

      logic      SEL;

      assign data_req_o    =     data_req0_i | data_req1_i;
      assign SEL           =    ~data_req0_i | ( RR_FLAG & data_req1_i);      // SEL FOR ROUND ROBIN MUX

      // Grant gnt0 and gnt1
      assign data_gnt0_o   =    (( data_req0_i & ~data_req1_i) | ( data_req0_i & ~RR_FLAG)) & data_gnt_i;
      assign data_gnt1_o   =    ((~data_req0_i &  data_req1_i) | ( data_req1_i &  RR_FLAG)) & data_gnt_i;    

      //MUXES AND DEMUXES 
      always_comb
      begin : FanIn_MUX2
          case(SEL) //synopsys full_case
          1'b0:
          begin //PRIORITY ON CH_0
              data_operand_o = data_operand0_i;
              data_op_o      = data_op0_i;
              data_flag_o    = data_flag0_i;
              data_ID_o      = data_ID0_i;
          end

          1'b1:
          begin //PRIORITY ON CH_1
              data_operand_o = data_operand1_i;
              data_op_o      = data_op1_i;
              data_flag_o    = data_flag1_i;
              data_ID_o      = data_ID1_i;
          end
          endcase
      end
 
endmodule