// Copyright 2019 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

// Imported from WIP in axi repo; TODO: unify APB modules and depend on the updated apb repo

// APB Read-Write Registers
// TODO: Module specification

module apb_rw_regs #(
  parameter int unsigned ADDR_WIDTH = 0,
  parameter int unsigned DATA_WIDTH = 0,
  parameter int unsigned N_REGS     = 0
) (
  input  logic        clk_i,
  input  logic        rst_ni,

  // APB Interface
  APB_BUS.Slave       apb,

  // Register Interface
  input  logic [N_REGS-1:0][DATA_WIDTH-1:0] init_i,
  output logic [N_REGS-1:0][DATA_WIDTH-1:0] q_o
);

  localparam int unsigned STRB_WIDTH = DATA_WIDTH/8;
  localparam int unsigned WORD_OFF = $clog2(STRB_WIDTH);

  logic [N_REGS-1:0][DATA_WIDTH-1:0] reg_d, reg_q;

  always_comb begin
    reg_d       = reg_q;
    apb.prdata  = 'x;
    apb.pslverr = 1'b0;
    if (apb.psel) begin
      automatic logic [ADDR_WIDTH-WORD_OFF-1:0] word_addr = apb.paddr >> WORD_OFF;
      if (word_addr >= N_REGS) begin
        // Error response to accesses that are out of range
        apb.pslverr = 1'b1;
      end else begin
        if (apb.pwrite) begin
          reg_d[word_addr] = apb.pwdata;
          // TODO: handle after upgrade to APBv2
          //for (int i = 0; i < STRB_WIDTH; i++) begin
          //  if (apb.pstrb[i]) begin
          //    reg_d[word_addr][i*8 +: 8] = apb.pwdata[i*8 +: 8];
          //  end
          //end
        end else begin
          apb.prdata = reg_q[word_addr];
        end
      end
    end
  end
  assign apb.pready = apb.psel & apb.penable;

  assign q_o = reg_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reg_q <= init_i;
    end else begin
      reg_q <= reg_d;
    end
  end

  // Validate parameters.
  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      assert (N_REGS >= 1) else $fatal(1, "The number of registers must be at least 1!");
    end
  `endif
  // pragma translate_on

endmodule
