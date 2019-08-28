// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Company:        Multitherman Laboratory @ DEIS - University of Bologna     //
//                    Viale Risorgimento 2 40136                              //
//                    Bologna - fax 0512093785 -                              //
//                                                                            //
// Engineer:       Davide Rossi - davide.rossi@unibo.it                       //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
// Create Date:    13/02/2013                                                 // 
// Design Name:    ULPSoC                                                     // 
// Module Name:    ulpcluster_top                                             //
// Project Name:   ULPSoC                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    ULPSoC cluster                                             //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (10/04/2015) Register count reduced to only 2:             //
//                 0x00 --> PIPE_REGS[0] --> Store the PIPE REQ  enable vector//
//                 0x04 --> PIPE_REGS[1] --> Store the PIPE RESP enable vector//
// Revision v0.3 - (11/04/2015) Fixed some issues/errors                      //
// Revision v0.4 - (11/04/2015) removed 32 more FF for rdata. Now there there //
//                 a 2:1 Mux between registers and rdata, sel is FF driven    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`define log2(VALUE) ((VALUE) < ( 1 ) ? 0 : (VALUE) < ( 2 ) ? 1 : (VALUE) < ( 4 ) ? 2 : (VALUE)< (8) ? 3:(VALUE) < ( 16 )  ? 4 : (VALUE) < ( 32 )  ? 5 : (VALUE) < ( 64 )  ? 6 : (VALUE) < ( 128 ) ? 7 : (VALUE) < ( 256 ) ? 8 : (VALUE) < ( 512 ) ? 9 : 10)

module tcdm_pipe_unit
#(
    parameter  N_SLAVE = 16,
    parameter  ID_WIDTH = 5
)
(
    input logic                         clk_i,
    input logic                         rst_ni,

    XBAR_PERIPH_BUS.Slave               speriph_slave,

    output logic [N_SLAVE-1:0]          enable_resp_pipe_o,
    output logic [N_SLAVE-1:0]          enable_req_pipe_o
);
    localparam                  NUM_REGS     = 2;                       // DONT CHANGE unless you know what you are doin. OUTPUT are hard wired to reg[0] and reg[1]
    localparam                  LOG_NUM_REGS = `log2(NUM_REGS-1);       // DONT CHANGE unless you know what you are doin

    //[byte-1:0][bit-1:0]
    logic [3:0][7:0]             PIPE_REGS[NUM_REGS]; // PIPE_REGS
    logic [NUM_REGS-1:0][31:0]   PIPE_REGS_32; // Copy of PIPE_REGS

    integer i,j;
    genvar k;

    // Exploded Interface
    logic                req;
    logic [31:0]         addr;
    logic                wen;
    logic [3:0][7:0]     wdata;
    logic [3:0]          be;
    logic                gnt;
    logic [ID_WIDTH-1:0] id;

    logic                r_valid;
    logic                r_opc;
    logic [ID_WIDTH-1:0] r_id;
    logic [31:0]         r_rdata;

    logic [LOG_NUM_REGS-1:0]    dest_reg_q;

    assign r_rdata = PIPE_REGS[dest_reg_q];

    generate
        for(k=0; k<NUM_REGS; k++)
        begin
            assign PIPE_REGS_32[k] = PIPE_REGS[k];
        end
    endgenerate

    assign enable_req_pipe_o  = PIPE_REGS_32[0][N_SLAVE-1:0];
    assign enable_resp_pipe_o = PIPE_REGS_32[1][N_SLAVE-1:0];

    assign gnt = 1'b1; // Always ready peripheral

    // ------------ INTERFACE BINDING  -------------------//
    assign speriph_slave.gnt = gnt;
    assign req   = speriph_slave.req;
    assign addr  = speriph_slave.add;
    assign wen   = speriph_slave.wen;
    assign wdata = speriph_slave.wdata;
    assign be    = speriph_slave.be;
    assign id    = speriph_slave.id[ID_WIDTH-1:0];


    assign speriph_slave.r_valid = r_valid;
    assign speriph_slave.r_opc   = r_opc;
    assign speriph_slave.r_id[ID_WIDTH-1:0] = r_id;
    assign speriph_slave.r_rdata = r_rdata;
   // ------- END OF  INTERFACE BINDING  ----------------//


    // UPDATE THE STATE
    always_ff @(posedge clk_i, negedge  rst_ni)
    begin : UPDATE_STATE
        if(rst_ni == 1'b0)
        begin
            for(i=0;i<NUM_REGS;i++)
            begin : reset_PIPE
              PIPE_REGS[i] <= '0;
            end
            r_valid <= 1'b0;
            r_opc   <= 1'b0;
            r_id    <= '0;
            //r_rdata <= '0;
            dest_reg_q <= '0;
        end
        else
        begin

            r_opc   <= 1'b0;
            if(req)
            begin
                    r_valid <= 1'b1;
                    r_id    <= id;

                    if(wen == 1'b0)
                    begin
                          for(i=0; i<4; i++)
                          begin
                            if(be[i])
                              PIPE_REGS[addr[LOG_NUM_REGS+2-1:2]][i] <= wdata[i];
                          end
                          //r_rdata <= 'X;
                    end
                    else
                    begin
                          //r_rdata <= PIPE_REGS[addr[LOG_NUM_REGS+2-1:2]];
                          dest_reg_q <= addr[LOG_NUM_REGS+2-1:2];
                    end
            end
            else
            begin
                    //r_rdata <= 'X;
                    r_valid <= 1'b0;
                    r_id    <= '0;
            end
        end
    end
endmodule
