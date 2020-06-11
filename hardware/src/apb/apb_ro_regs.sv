// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

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
