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
// Module Name:    fpnew_wrapper                                              //
// Project Name:   VEGA                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    wrapper for fpnew system verilog block                     //
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



import riscv_defines::*;
// `define DUMMY_FPNEW

module fpnew_wrapper
#(
  parameter ID_WIDTH         = 9,
  parameter NB_ARGS          = 2,
  parameter OPCODE_WIDTH     = 6,
  parameter DATA_WIDTH       = 32,
  parameter FLAGS_IN_WIDTH   = 15,
  parameter FLAGS_OUT_WIDTH  = 5,
  parameter C_FPNEW_FMTBITS  = fpnew_pkg::FP_FORMAT_BITS,
  parameter C_FPNEW_IFMTBITS = fpnew_pkg::INT_FORMAT_BITS,
  parameter C_ROUND_BITS     = 3,
  parameter C_FPNEW_OPBITS   = fpnew_pkg::OP_BITS,
  parameter FP_DIVSQRT       = 0
)
(
   // Clock and Reset
   input  logic                                   clk,
   input  logic                                   rst_n,

   // APU Side: Master port
   input  logic                                   apu_req_i,
   output logic                                   apu_gnt_o,
   input  logic [ID_WIDTH-1:0]                    apu_ID_i, // not used

   // request channel
   input  logic [NB_ARGS-1:0][DATA_WIDTH-1:0]     apu_operands_i,
   input  logic [OPCODE_WIDTH-1:0]                apu_op_i,
   input  logic [FLAGS_IN_WIDTH-1:0]              apu_flags_i,

   // response channel
   input  logic                                   apu_rready_i, // not used
   output logic                                   apu_rvalid_o,
   output logic [DATA_WIDTH-1:0]                  apu_rdata_o,
   output logic [FLAGS_OUT_WIDTH-1:0]             apu_rflags_o,
   output logic [ID_WIDTH-1:0]                    apu_rID_o // not used
);

   `ifdef DUMMY_FPNEW
         always_ff @(posedge clk or negedge rst_n)
         begin : proc_
            if(~rst_n) begin
                apu_gnt_o    = '0;
                apu_rvalid_o = '0;
                apu_rdata_o  = '0;
                apu_rflags_o = '0;
                apu_rID_o    = '0;
            end else begin
                apu_gnt_o    = 1'b1;
                apu_rvalid_o = (apu_gnt_o & apu_req_i);
                apu_rdata_o  = 32'hC1A0C1A0;
                apu_rflags_o = '1;
                apu_rID_o    = apu_ID_i;
            end
         end
   `else

        localparam C_DIV = FP_DIVSQRT ? fpnew_pkg::MERGED : fpnew_pkg::DISABLED;

         logic [C_FPNEW_OPBITS-1:0]   fpu_op;
         logic                        fpu_op_mod;
         logic                        fpu_vec_op;

         logic [C_FPNEW_FMTBITS-1:0]  dst_fmt;
         logic [C_FPNEW_FMTBITS-1:0]  src_fmt;
         logic [C_FPNEW_IFMTBITS-1:0] int_fmt;
         logic [C_ROUND_BITS-1:0]     fp_rnd_mode;

         // assign apu_rID_o = '0;
         assign {fpu_vec_op, fpu_op_mod, fpu_op} = apu_op_i;
         assign {int_fmt, src_fmt, dst_fmt, fp_rnd_mode} = apu_flags_i;


        // -----------
        // FPU Config
        // -----------
        // Features (enabled formats, vectors etc.)
        localparam fpnew_pkg::fpu_features_t FPU_FEATURES = '{
          Width:         C_FLEN,
          EnableVectors: C_XFVEC,
          EnableNanBox:  1'b0,
          FpFmtMask:     {C_RVF, C_RVD, C_XF16, C_XF8, C_XF16ALT},
          IntFmtMask:    {C_XFVEC && C_XF8, C_XFVEC && (C_XF16 || C_XF16ALT), 1'b1, 1'b0}
        };

        // Implementation (number of registers etc)
        localparam fpnew_pkg::fpu_implementation_t FPU_IMPLEMENTATION = '{
          PipeRegs:  '{// FP32, FP64, FP16, FP8, FP16alt
                       '{C_LAT_FP32, C_LAT_FP64, C_LAT_FP16, C_LAT_FP8, C_LAT_FP16ALT}, // ADDMUL
                       '{default: C_LAT_DIVSQRT}, // DIVSQRT
                       '{default: C_LAT_NONCOMP}, // NONCOMP
                       '{default: C_LAT_CONV}},   // CONV
          UnitTypes: '{'{default: fpnew_pkg::MERGED}, // ADDMUL
                       '{default: C_DIV},               // DIVSQRT
                       '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                       '{default: fpnew_pkg::MERGED}},  // CONV
          PipeConfig: fpnew_pkg::BEFORE
        };

        //---------------
        // FPU instance
        //---------------
        fpnew_top #(
          .Features       ( FPU_FEATURES         ),
          .Implementation ( FPU_IMPLEMENTATION   ),
          .TagType        ( logic [ID_WIDTH-1:0] )
        ) i_fpnew (
          .clk_i          ( clk                                  ),
          .rst_ni         ( rst_n                                ),
          .operands_i     ( apu_operands_i                       ),
          .rnd_mode_i     ( fpnew_pkg::roundmode_e'(fp_rnd_mode) ),
          .op_i           ( fpnew_pkg::operation_e'(fpu_op)      ),
          .op_mod_i       ( fpu_op_mod                           ),
          .src_fmt_i      ( fpnew_pkg::fp_format_e'(src_fmt)     ),
          .dst_fmt_i      ( fpnew_pkg::fp_format_e'(dst_fmt)     ),
          .int_fmt_i      ( fpnew_pkg::int_format_e'(int_fmt)    ),
          .vectorial_op_i ( fpu_vec_op                           ),
          .tag_i          ( apu_ID_i                             ),
          .in_valid_i     ( apu_req_i                            ),
          .in_ready_o     ( apu_gnt_o                            ),
          .flush_i        ( 1'b0                                 ),
          .result_o       ( apu_rdata_o                          ),
          .status_o       ( apu_rflags_o                         ),
          .tag_o          ( apu_rID_o                            ),
          .out_valid_o    ( apu_rvalid_o                         ),
          .out_ready_i    ( 1'b1                                 ),
          .busy_o         ( /* unused */                         )
        );


  `endif
endmodule // fpnew_wrapper
