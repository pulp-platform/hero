// Copyright 2019 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

// Imported from WIP in axi repo; TODO: unify APB modules and depend on the updated apb repo

// APB Bus with Single Master and Multiple Slave Interfaces
// Each slave is accessible at exactly one address segment, and the address ranges of no two slaves
// may overlap. If the input address of this bus is not in any slave address segment, the bus
// responds with slverr; otherwise, this bus feeds all signals through to the slave. The slaves see
// offset-compensated addresses, e.g., if this bus gets ADDR_BEGIN[i] as input address, slave i will
// get address 0.
module apb_bus #(
  // Number of slaves.
  parameter int unsigned ADDR_WIDTH = 0,
  parameter int unsigned DATA_WIDTH = 0,
  parameter int unsigned N_SLV      = 0,
  // Address ranges of the slaves. Slave i is mapped in the inclusive interval from ADDR_BEGIN[i] to
  // ADDR_END[i].
  parameter logic [N_SLV-1:0][ADDR_WIDTH-1:0] ADDR_BEGIN  = '0,
  parameter logic [N_SLV-1:0][ADDR_WIDTH-1:0] ADDR_END    = '0,
  // Dependent parameters, do not change!
  parameter int unsigned STRB_WIDTH = DATA_WIDTH/8
) (
  // Input
  input  logic            [ADDR_WIDTH-1:0]  paddr_i,
  input  logic                       [2:0]  pprot_i,
  input  logic                              psel_i,
  input  logic                              penable_i,
  input  logic                              pwrite_i,
  input  logic            [DATA_WIDTH-1:0]  pwdata_i,
  input  logic            [STRB_WIDTH-1:0]  pstrb_i,
  output logic                              pready_o,
  output logic            [DATA_WIDTH-1:0]  prdata_o,
  output logic                              pslverr_o,

  // Outputs
  output logic [N_SLV-1:0][ADDR_WIDTH-1:0]  paddr_o,
  output logic [N_SLV-1:0]           [2:0]  pprot_o,
  output logic [N_SLV-1:0]                  psel_o,
  output logic [N_SLV-1:0]                  penable_o,
  output logic [N_SLV-1:0]                  pwrite_o,
  output logic [N_SLV-1:0][DATA_WIDTH-1:0]  pwdata_o,
  output logic [N_SLV-1:0][STRB_WIDTH-1:0]  pstrb_o,
  input  logic [N_SLV-1:0]                  pready_i,
  input  logic [N_SLV-1:0][DATA_WIDTH-1:0]  prdata_i,
  input  logic [N_SLV-1:0]                  pslverr_i
);

  logic [$clog2(N_SLV)-1:0] sel_idx;
  logic dec_err;

  for (genvar i = 0; i < N_SLV; i++) begin: gen_oup_demux
    assign paddr_o[i]   = paddr_i - ADDR_BEGIN[i];
    assign pprot_o[i]   = pprot_i;
    assign psel_o[i]    = psel_i & (paddr_i >= ADDR_BEGIN[i] && paddr_i <= ADDR_END[i]);
    assign penable_o[i] = penable_i;
    assign pwrite_o[i]  = pwrite_i;
    assign pwdata_o[i]  = pwdata_i;
    assign pstrb_o[i]   = pstrb_i;
  end

  assign dec_err = psel_i & ~(|psel_o);

  if (N_SLV > 1) begin: gen_sel_idx_onehot
    onehot_to_bin #(.ONEHOT_WIDTH(N_SLV)) i_sel_idx (
      .onehot (psel_o),
      .bin    (sel_idx)
    );
  end else begin: gen_sel_idx_zero
    assign sel_idx = 1'b0;
  end

  always_comb begin
    if (psel_i) begin
      if (dec_err) begin
        pready_o  = 1'b1;
        prdata_o  = '0;
        pslverr_o = 1'b1;
      end else begin
        pready_o  = pready_i[sel_idx];
        prdata_o  = prdata_i[sel_idx];
        pslverr_o = pslverr_i[sel_idx];
      end
    end else begin // !psel_i
      pready_o  = 1'b0;
      prdata_o  = '0;
      pslverr_o = 1'b0;
    end
  end

  // Validate parameters.
  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      assert (N_SLV >= 1) else $fatal(1, "The number of slave ports must be at least 1!");
      assert (ADDR_WIDTH >= 1) else $fatal(1, "The addr width must be at least 1!");
      assert (DATA_WIDTH >= 1) else $fatal(1, "The data width must be at least 1!");
    end
    for (genvar i = 0; i < N_SLV; i++) begin: gen_assert_addr_outer
      initial begin
        assert (ADDR_BEGIN[i] <= ADDR_END[i])
          else $fatal(1, "Invalid address range for slave %0d", i);
      end
      for (genvar j = 0; j < N_SLV; j++) begin: gen_assert_addr_inner
        initial begin
          if (i != j) begin
            if (ADDR_BEGIN[j] >= ADDR_BEGIN[i]) begin
              assert (ADDR_BEGIN[j] > ADDR_END[i])
                else $fatal("Address range of slaves %0d and %0d overlap!", i, j);
            end else begin
              assert (ADDR_END[j] < ADDR_BEGIN[i])
                else $fatal("Address range of slaves %0d and %0d overlap!", i, j);
            end
          end
        end
      end
    end
  `endif
  // pragma translate_on

endmodule
