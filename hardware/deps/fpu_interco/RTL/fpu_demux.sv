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
// Module Name:    fpu_demux                                                  //
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

module fpu_demux
#(
    parameter DATA_WIDTH         = 32,
    parameter FP_TYPE_WIDTH       = 5,
    parameter NB_CORE_ARGS        = 3,
    parameter CORE_OPCODE_WIDTH   = 6,
    parameter CORE_DSFLAGS_CPU    = 15,
    parameter CORE_USFLAGS_CPU    = 5,

    parameter NB_APU_ARGS        = 3,
    parameter APU_OPCODE_WIDTH   = 6,
    parameter APU_DSFLAGS_CPU    = 15,
    parameter APU_USFLAGS_CPU    = 5,

    parameter NB_FPNEW_ARGS        = 3,
    parameter FPNEW_OPCODE_WIDTH   = 6,
    parameter FPNEW_DSFLAGS_CPU    = 15,
    parameter FPNEW_USFLAGS_CPU    = 5,

    parameter APU_ID   = 1,
    parameter FPNEW_ID = 0
)
(
   input logic                                          clk,
   input logic                                          rst_n,

   // CORE SIDE: Slave port
   input  logic                                         core_slave_req_i,
   output logic                                         core_slave_gnt_o,
   input  logic [FP_TYPE_WIDTH-1:0]                     core_slave_type_i,
   // request channel
   input logic [NB_CORE_ARGS-1:0][DATA_WIDTH-1:0]       core_slave_operands_i,
   input logic [CORE_OPCODE_WIDTH-1:0]                  core_slave_op_i,
   input logic [CORE_DSFLAGS_CPU-1:0]                   core_slave_flags_i,
   // response channel
   input  logic                                         core_slave_rready_i,
   output logic                                         core_slave_rvalid_o,
   output logic [DATA_WIDTH-1:0]                        core_slave_rdata_o,
   output logic [CORE_USFLAGS_CPU-1:0]                  core_slave_rflags_o,




   // APU Side: Master port
   output logic                                          apu_req_o,
   input  logic                                          apu_gnt_i,
   // request channel
   output logic [NB_APU_ARGS-1:0][DATA_WIDTH-1:0]        apu_operands_o,
   output logic [APU_OPCODE_WIDTH-1:0]                   apu_op_o,
   output logic [APU_DSFLAGS_CPU-1:0]                    apu_flags_o,
   // response channel
   output logic                                          apu_rready_o,
   input  logic                                          apu_rvalid_i,
   input  logic [DATA_WIDTH-1:0]                         apu_rdata_i,
   input  logic [APU_USFLAGS_CPU-1:0]                    apu_rflags_i,



   // FPNEW Side: Master port
   output logic                                          fpnew_req_o,
   input  logic                                          fpnew_gnt_i,
   // request channel
   output logic [NB_FPNEW_ARGS-1:0][DATA_WIDTH-1:0]      fpnew_operands_o,
   output logic [FPNEW_OPCODE_WIDTH-1:0]                 fpnew_op_o,
   output logic [FPNEW_DSFLAGS_CPU-1:0]                  fpnew_flags_o,
   // response channel
   output logic                                          fpnew_rready_o,
   input  logic                                          fpnew_rvalid_i,
   input  logic [DATA_WIDTH-1:0]                         fpnew_rdata_i,
   input  logic [FPNEW_USFLAGS_CPU-1:0]                  fpnew_rflags_i
);


    enum logic [1:0] {IDLE, WAIT_APU_RVALID, WAIT_FPNEW_RVALID, ERROR } CS, NS;


    always_ff @(posedge clk or negedge rst_n)
    begin
        if(~rst_n)
        begin
             CS <= IDLE;
        end
        else
        begin
             CS <= NS;
        end
    end



    always_comb
    begin
        apu_req_o        = '0;
        apu_operands_o   = core_slave_operands_i[NB_APU_ARGS-1:0];
        apu_op_o         = core_slave_op_i[APU_OPCODE_WIDTH-1:0];
        apu_flags_o      = core_slave_flags_i[APU_DSFLAGS_CPU-1:0];
        apu_rready_o     = '0;

        fpnew_req_o      = '0;
        fpnew_operands_o = core_slave_operands_i[NB_FPNEW_ARGS-1:0];
        fpnew_op_o       = core_slave_op_i[FPNEW_OPCODE_WIDTH-1:0];
        fpnew_flags_o    = core_slave_flags_i[FPNEW_DSFLAGS_CPU-1:0];
        fpnew_rready_o   = '0;

        core_slave_rvalid_o  = '0;
        core_slave_rdata_o   = '0;
        core_slave_rflags_o  = '0;
        core_slave_gnt_o     = 1'b0;

        NS = CS;

        case(CS)

            IDLE:
            begin
                if(core_slave_req_i)
                begin
                    case(core_slave_type_i)
                    APU_ID:
                    begin
                        apu_req_o         = 1'b1;
                        core_slave_gnt_o  = apu_gnt_i;

                        apu_rready_o = core_slave_rready_i;

                        core_slave_rvalid_o  = apu_rvalid_i;
                        core_slave_rdata_o   = apu_rdata_i;
                        core_slave_rflags_o  = apu_rflags_i;                         

                        case({apu_rvalid_i,apu_gnt_i})
                            2'b01: NS = WAIT_APU_RVALID;
                            2'b11: NS = IDLE;
                            2'b00: NS = IDLE;
                            2'b10: NS = IDLE;
                        endcase // {apu_rvalid_i,apu_gnt_i}
                    end


                    FPNEW_ID:
                    begin
                        fpnew_req_o       = 1'b1;
                        core_slave_gnt_o  = fpnew_gnt_i;
                        fpnew_rready_o    = core_slave_rready_i;

                        core_slave_rvalid_o  = fpnew_rvalid_i;
                        core_slave_rdata_o   = fpnew_rdata_i;
                        core_slave_rflags_o  = fpnew_rflags_i;                        

                        case({fpnew_rvalid_i,fpnew_gnt_i})
                            2'b01: NS = WAIT_FPNEW_RVALID;
                            2'b11: NS = IDLE;
                            2'b00: NS = IDLE;
                            2'b10: NS = IDLE;
                        endcase // {apu_rvalid_i,apu_gnt_i}

                    end

                    default:
                    begin
                        NS = ERROR;
                        core_slave_gnt_o = 1'b1;
                    end

                    endcase // core_slave_type_i

                end
                else // no request
                begin
                    NS = IDLE;
                end

            end




            WAIT_APU_RVALID:
            begin
                core_slave_rvalid_o  = apu_rvalid_i;
                core_slave_rdata_o   = apu_rdata_i;
                core_slave_rflags_o  = apu_rflags_i;  

                if(apu_rvalid_i)
                begin
                    NS = IDLE;
                end
                else
                begin
                    NS = WAIT_APU_RVALID;
                end


            end

            WAIT_FPNEW_RVALID:
            begin
                core_slave_rvalid_o  = fpnew_rvalid_i;
                core_slave_rdata_o   = fpnew_rdata_i;
                core_slave_rflags_o  = fpnew_rflags_i;  

                if(fpnew_rvalid_i)
                begin
                    NS = IDLE;
                end
                else
                begin
                    NS = WAIT_FPNEW_RVALID;
                end


            end




            ERROR:
            begin
                core_slave_rvalid_o  = 1'b1;
                core_slave_rdata_o   = 32'hBAD_F7_ACC;
                core_slave_rflags_o  = '0;  
                NS                   = IDLE;
            end

        endcase // CS

    end





endmodule
