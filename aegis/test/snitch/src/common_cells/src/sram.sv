// Copyright 2017, 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Date: 13.10.2017
// Description: SRAM Behavioral Model

module sram #(
    parameter int unsigned DATA_WIDTH = 64,
    parameter int unsigned NUM_WORDS  = 1024,
    parameter bit OUT_REGS            = 0, // enables output registers in FPGA macro (read lat = 2)
    parameter int SIM_INIT            = 2
)(
   input  logic                          clk_i,
   input  logic                          rst_ni,

   input  logic                          req_i,
   input  logic                          we_i,
   input  logic [$clog2(NUM_WORDS)-1:0]  addr_i,
   input  logic [DATA_WIDTH-1:0]         wdata_i,
   input  logic [(DATA_WIDTH+7)/8-1:0]   be_i,
   output logic [DATA_WIDTH-1:0]         rdata_o
);
    localparam ADDR_WIDTH = $clog2(NUM_WORDS);

    logic [DATA_WIDTH-1:0] ram [NUM_WORDS-1:0];
    logic [ADDR_WIDTH-1:0] raddr_q, raddr_qq;

    // 1. randomize array
    // 2. randomize output when no request is active
    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (!rst_ni) begin
          for (int i = 0; i < NUM_WORDS; i++) ram[i] <= '0;
        end else begin
          if (req_i) begin
              raddr_q <= addr_i;
              for (int i = 0; i < (DATA_WIDTH+7)/8; i++) begin
                if (we_i && be_i[i]) ram[addr_i][i * 8 +: 8] <= wdata_i[i * 8 +: 8];
              end
          end
        end
    end

    if (OUT_REGS) begin
      always_ff @(posedge clk_i) begin : proc_
        rdata_o <= ram[raddr_q];
      end
    end else begin
      assign rdata_o = ram[raddr_q];
    end

    initial begin
      $display("Width: %d Depth: %d", DATA_WIDTH, NUM_WORDS);
    end
endmodule
