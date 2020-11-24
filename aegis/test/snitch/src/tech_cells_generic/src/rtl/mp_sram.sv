// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba    <zarubaf@iis.ee.ethz.ch>, ETH Zurich
//         Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: Multi-Ported SRAM
//
module mp_sram #(
    parameter int unsigned DataWidth = 64,
    parameter int unsigned NumWords  = 1024,
    parameter bit          OutRegs   = 0,   // enables output registers in FPGA macro (read lat = 2)
    parameter logic [1:0]  SimInit   = 0,   // for simulation only, will not be synthesized
                                            // 0: no init, 1: zero init, 2: random init
                                            // note: on verilator, 2 is not supported. define the VERILATOR macro to work around.
    parameter int unsigned NrPorts   = 2
)(
   input  logic                              clk_i,
   input  logic                              rst_ni, // reset - together with the SimInit variable determines the initialization value
   input  logic [1:0]                        req_i,  // request to read or write - active high
   input  logic [1:0]                        we_i,   // write enable - active high
   input  logic [1:0][$clog2(NumWords)-1:0]  addr_i,
   input  logic [1:0][DataWidth-1:0]         wdata_i,
   input  logic [1:0][(DataWidth+7)/8-1:0]   be_i,
   output logic [1:0][DataWidth-1:0]         rdata_o,
   input  logic [1:0]                        inject_s_biterror_i, // only working for non-verilator simulation
   input  logic [1:0]                        inject_d_biterror_i
);

localparam DataWidthAligned = ((DataWidth+7)/8)*8;
localparam BeWidthAlgined   = (((DataWidth+7)/8+7)/8)*8;

logic [DataWidthAligned-1:0] mem_q [NumWords-1:0];

logic [1:0][DataWidth-1:0]         wdata_error;

logic [1:0][DataWidthAligned-1:0]  wdata_aligned;
logic [1:0][BeWidthAlgined-1:0]    be_aligned;
logic [1:0][DataWidthAligned-1:0]  rdata_q;
logic [1:0][DataWidthAligned-1:0]  rdata_qq;

`ifndef VERILATOR
always_comb begin
  wdata_error = '0;
  for (int i = 0; i < NrPorts; i++) begin
    if (inject_s_biterror_i) begin
      // flip a bit somewhere in the word
      wdata_error[i] = 1'b1 << $urandom_range(DataWidth, 0);
    end else if (inject_d_biterror_i) begin
      // flip two bits somewhere in the word, this might just flip one if the random numbers turn out to be
      // the same
      wdata_erro[i] = (1'b1 << $urandom_range(DataWidth, 0)) | (1'b1 << $urandom_range(DataWidth, 0));
    end
  end
end
`else
assign wdata_error = '0;
`endif

  // align to 8 bits for inferable macro below
  always_comb begin : p_align
    for (int i = 0; i < NrPorts; i++) begin
      wdata_aligned[i]                    = '0;
      be_aligned[i]                       = '0;
      wdata_aligned[i][DataWidth-1:0]     = wdata_i[i];
      be_aligned[i][BeWidthAlgined-1:0]   = be_i[i];

      rdata_o[i] = rdata_qq[i][DataWidth-1:0];
    end
  end

  always_ff @(posedge clk_i) begin
    // pragma translate_off
    // sim initialization
    automatic logic [DataWidthAligned-1:0] val;

    if (!rst_ni && SimInit > 0) begin
      for (int k = 0; k < NumWords; k++) begin
        // initialize to zero
        if (SimInit == 1) val = '0;
`ifndef VERILATOR
        // randomize content
        else if (SimInit == 2) void'(randomize(val));
`endif
        mem_q[k] = val;
      end
    end else
    // pragma translate_on
    for (int i = 0; i < NrPorts; i++) begin
      if (req_i[i]) begin
        if (we_i[i]) begin
          for (int j = 0; j < $size(be_aligned); j++) begin
            if (be_aligned[i][j]) mem_q[addr_i[i]][j*8 +: 8] <= wdata_aligned[i][j*8 +: 8];
          end
        end else begin
          rdata_q[i] <= mem_q[addr_i[i]];
        end
      end
    end
  end

  // optional output regs
  if (OutRegs > 0) begin : output_register
    for (genvar i = 0; i < NrPorts; i++) begin
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          rdata_qq[i]  <= '0;
        end else begin
          rdata_qq[i]  <= rdata_q[i];
        end
      end
    end
  // output reg bypass
  end else begin : no_output_register
    for (genvar i = 0; i < NrPorts; i++) assign rdata_qq[i]  = rdata_q[i];
  end
endmodule
