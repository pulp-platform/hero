// Copyright 2019 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

// Imported from WIP in axi repo; TODO: unify APB modules and depend on the updated apb repo

// APB Read-Only Registers
// TODO: Module specification

module apb_ro_regs #(
  parameter int unsigned ADDR_WIDTH = 0,
  parameter int unsigned DATA_WIDTH = 0,
  parameter int unsigned N_REGS     = 0
) (
  APB_BUS.Slave                             apb,
  input  logic [N_REGS-1:0][DATA_WIDTH-1:0] reg_i
);

  localparam WORD_OFF = $clog2(DATA_WIDTH/8);

  always_comb begin
    apb.prdata  = 'x;
    apb.pslverr = 1'b0;
    if (apb.psel) begin
      if (apb.pwrite) begin
        // Error response to writes
        apb.pslverr = 1'b1;
      end else begin
        automatic logic [ADDR_WIDTH-WORD_OFF-1:0] word_addr = apb.paddr >> WORD_OFF;
        if (word_addr >= N_REGS) begin
          // Error response to reads out of range
          apb.pslverr = 1'b1;
        end else begin
          apb.prdata = reg_i[word_addr];
        end
      end
    end
  end
  assign apb.pready = apb.psel & apb.penable;

  // Validate parameters.
  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      assert (N_REGS >= 1) else $fatal(1, "The number of registers must be at least 1!");
    end
  `endif
  // pragma translate_on

endmodule
