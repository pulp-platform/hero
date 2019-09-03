// Copyright 2019 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

// TODO: Replace behavior with instantiation of cuts.

module sram #(
  parameter int unsigned DATA_WIDTH = 0,   // [bit]
  parameter int unsigned N_WORDS    = 0,
  // Dependent parameters, do not override!
  parameter int unsigned N_BYTES = DATA_WIDTH/8,
  parameter type addr_t = logic[$clog2(N_WORDS)-1:0],
  parameter type data_t = logic[DATA_WIDTH-1:0],
  parameter type strb_t = logic[N_BYTES-1:0]
) (
  input  logic  clk_i,
  input  logic  rst_ni,
  input  logic  req_i,
  input  logic  we_i,
  input  addr_t addr_i,
  input  data_t wdata_i,
  input  strb_t be_i,
  output data_t rdata_o
);

`ifdef TARGET_SYNTHESIS
  $fatal(1, "Unsupported synthesis target!");

`else // behavioral
  data_t mem [N_WORDS-1:0];
  always_ff @(posedge clk_i) begin
    if (req_i) begin
      if (we_i) begin
        for (int unsigned i = 0; i < N_BYTES; i++) begin
          if (be_i[i]) begin
            mem[addr_i][i*8+:8] <= wdata_i[i*8+:8];
          end
        end
      end else begin
        rdata_o <= mem[addr_i];
      end
    end
  end
`endif

endmodule
