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
// Create Date:    19/01/2019                                                 //
// Design Name:    FPU_INTERCONNECT                                           //
// Module Name:    fp_iter_divsqrt_msv_wrapper_2_STAGE                        //
// Project Name:   VEGA                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    wrapper for fpu sqrt-div system verilog block              //
//                                                                            //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 19/01/2019 : File Created                                  //
//                                                                            //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module fp_iter_divsqrt_msv_wrapper_2_STAGE
#(
  parameter ID_WIDTH        = 9,
  parameter NB_ARGS         = 2,
  parameter DATA_WIDTH      = 32,
  parameter OPCODE_WIDTH    = 1,
  parameter FLAGS_IN_WIDTH  = 3,
  parameter FLAGS_OUT_WIDTH = 5
)
(
   // Clock and Reset
   input  logic                               clk,
   input  logic                               rst_n,

   // APU Side: Master port
   input  logic                               apu_req_i,
   output logic                               apu_gnt_o,
   input  logic [ID_WIDTH-1:0]                apu_ID_i,

   // request channel
   input  logic [NB_ARGS-1:0][DATA_WIDTH-1:0] apu_operands_i,
   input  logic [OPCODE_WIDTH-1:0]            apu_op_i,
   input  logic [FLAGS_IN_WIDTH-1:0]          apu_flags_i,

   // response channel
   input  logic                               apu_rready_i, // not used
   output logic                               apu_rvalid_o,
   output logic [DATA_WIDTH-1:0]              apu_rdata_o,
   output logic [FLAGS_OUT_WIDTH-1:0]         apu_rflags_o,
   output logic [ID_WIDTH-1:0]                apu_rID_o
);

   logic                 div_start;
   logic                 sqrt_start;

   logic                 div_zero;
   logic                 exp_of;
   logic                 exp_uf;
   
   logic [NB_ARGS-1:0][DATA_WIDTH-1:0]   apu_operands_Q;
   logic [OPCODE_WIDTH-1:0]              apu_op_Q;
   logic [FLAGS_IN_WIDTH-1:0]            apu_flags_Q;
   logic                                 sample_data;
   logic                                 apu_gnt_int;

   logic [1:0]                           apu_rvalid_pipe_Q;
   logic [1:0][DATA_WIDTH-1:0]           apu_rdata_pipe_Q;
   logic [1:0][FLAGS_OUT_WIDTH-1:0]      apu_rflags_pipe_Q;
   logic [1:0][ID_WIDTH-1:0]             apu_rID_pipe_Q;

   logic                             apu_rvalid_int;
   logic [63:0]                      apu_rdata_int;
   logic [FLAGS_OUT_WIDTH-1:0]       apu_rflags_int;
   logic [ID_WIDTH-1:0]              apu_rID_int;

   enum logic [1:0] { IDLE, RUNNING , INIT_FPU } CS, NS;


  div_sqrt_top_mvp i_fp_iter_divsqrt_msv_wrapper_2_STAGE
  (
   .Clk_CI           ( clk                                 ), //input logic                            
   .Rst_RBI          ( rst_n                               ), //input logic                            
   .Div_start_SI     ( div_start                           ), //input logic                            
   .Sqrt_start_SI    ( sqrt_start                          ), //input logic                            
   .Operand_a_DI     ( {32'h0000_0000, apu_operands_Q[0]}  ), //input logic [C_OP_FP64-1:0]  // FIXME IS OK for 32bit only        
   .Operand_b_DI     ( {32'h0000_0000, apu_operands_Q[1]}  ), //input logic [C_OP_FP64-1:0]  // FIXME IS OK for 32bit only        
   .RM_SI            ( apu_flags_Q[2:0]                    ), //input logic [C_RM-1:0]  // Rounding Mode   
   .Precision_ctl_SI ( '0                                  ), //input logic [C_PC-1:0]  // Precision Control 

   .Format_sel_SI    ( apu_flags_Q[4:3]                    ), //input logic [C_FS-1:0]  // Format Selection,
   .Kill_SI          ( 1'b0                                ), //input logic                            

   .Result_DO        ( apu_rdata_int                       ), //output logic [C_OP_FP64-1:0]           

   .Fflags_SO        ( apu_rflags_int[4:0]                 ), //output logic [4:0]                     
   .Ready_SO         ( apu_gnt_int                         ), //output logic                           
   .Done_SO          ( apu_rvalid_int                      )  //output logic                           
 );



   assign apu_rvalid_o = apu_rvalid_pipe_Q[1];
   assign apu_rdata_o  = apu_rdata_pipe_Q [1];
   assign apu_rflags_o = apu_rflags_pipe_Q[1];
   assign apu_rID_o    = apu_rID_pipe_Q   [1];


   always_ff @(posedge clk or negedge rst_n)
   begin
         if(~rst_n)
         begin
            apu_rID_int        <= '0;
            apu_operands_Q     <= '0;
            apu_op_Q           <= '0;
            apu_flags_Q        <= '0;
            CS                 <= IDLE;
            apu_rvalid_pipe_Q  <= '0;
            apu_rdata_pipe_Q   <= '0;
            apu_rflags_pipe_Q  <= '0;
            apu_rID_pipe_Q     <= '0;
         end 
         else 
         begin
            CS <= NS;
            if(sample_data)
            begin
               apu_rID_int     <= apu_ID_i;
               apu_operands_Q  <= apu_operands_i;
               apu_op_Q        <= apu_op_i;
               apu_flags_Q     <= apu_flags_i;
            end

            apu_rvalid_pipe_Q[0] <= apu_rvalid_int;
            apu_rdata_pipe_Q [0] <= apu_rdata_int[DATA_WIDTH-1:0];
            apu_rflags_pipe_Q[0] <= apu_rflags_int;
            apu_rID_pipe_Q   [0] <= apu_rID_int;

            apu_rvalid_pipe_Q[1] <= apu_rvalid_pipe_Q[0];
            apu_rdata_pipe_Q [1] <= apu_rdata_pipe_Q [0];
            apu_rflags_pipe_Q[1] <= apu_rflags_pipe_Q[0];
            apu_rID_pipe_Q   [1] <= apu_rID_pipe_Q   [0];
         end

   end

   always_comb
   begin
      NS = CS;
      apu_gnt_o   = 1'b0;
      sample_data = 1'b0;
      div_start   = 1'b0;
      sqrt_start  = 1'b0;

      case(CS)
        IDLE:
        begin
          apu_gnt_o   = apu_gnt_int;
          sample_data = apu_req_i;

          if(apu_req_i & apu_gnt_o )
            NS = INIT_FPU;
          
        end

        INIT_FPU:
        begin
          NS = RUNNING;
          div_start  = ~apu_op_Q[0];
          sqrt_start =  apu_op_Q[0];
        end

        RUNNING:
        begin
          apu_gnt_o = 1'b0;

          if(apu_rvalid_o)
            NS = IDLE;
        end

        default:
        begin
          NS = IDLE;
        end
      endcase // CS
   end
   
endmodule
