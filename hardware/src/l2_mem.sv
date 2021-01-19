// Copyright 2019 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

`include "common_cells/registers.svh"

module l2_mem #(
  parameter int unsigned  AXI_AW = 0,   // [bit], must be a power of 2
  parameter int unsigned  AXI_DW = 0,   // [bit], must be a power of 2
  parameter int unsigned  AXI_IW = 0,   // [bit]
  parameter int unsigned  AXI_UW = 0,   // [bit]
  // Memory
  parameter int unsigned  N_BYTES = 0   // [B], must be a power of 2
) (
  input  logic  clk_i,
  input  logic  rst_ni,
  AXI_BUS.Slave slv
);

  // Types for entire memory array
  typedef logic   [AXI_AW-1:0] arr_addr_t;
  typedef logic   [AXI_DW-1:0] arr_data_t;
  typedef logic [AXI_DW/8-1:0] arr_strb_t;

  // Interface from AXI to memory array
  logic       req, req_q, we;
  arr_addr_t  addr;
  arr_data_t  wdata, rdata;
  arr_strb_t  be;

  axi2mem_wrap #(
    .AddrWidth  (AXI_AW),
    .DataWidth  (AXI_DW),
    .IdWidth    (AXI_IW),
    .UserWidth  (AXI_UW),
    .NumBanks   (1),
    .BufDepth   (1)
  ) i_axi2mem (
    .clk_i,
    .rst_ni,
    .busy_o       (/* unused */),
    .slv          (slv),
    .mem_req_o    (req),
    .mem_gnt_i    (1'b1),
    .mem_addr_o   (addr),
    .mem_wdata_o  (wdata),
    .mem_strb_o   (be),
    .mem_atop_o   (/* unused */),
    .mem_we_o     (we),
    .mem_rvalid_i (req_q),
    .mem_rdata_i  (rdata)
  );

  `ifdef TARGET_XILINX
    // Synthesis for Xilinx FPGAs can optimize SRAM tiling itself.
    localparam N_WORDS = N_BYTES / (AXI_DW/8);
    localparam LINE_OFF = $clog2(AXI_DW/8);
    tc_sram #(
      .NumWords   ( N_WORDS ), // specify explicitly for aegis!
      .DataWidth  ( AXI_DW  ), // specify explicitly for aegis!
      .ByteWidth  ( 8       ), // specify explicitly for aegis!
      .NumPorts   ( 1       )  // specify explicitly for aegis!
    ) i_tc_sram (
      .clk_i,
      .rst_ni,
      .req_i    (req),
      .we_i     (we),
      .addr_i   (addr[LINE_OFF+:$clog2(N_WORDS)]), // SRAM is row-addressed
      .wdata_i  (wdata),
      .be_i     (be),
      .rdata_o  (rdata)
    );

  `else
    // Properties of one memory cut, keep synchronized with instantiated macro.
    localparam int unsigned CUT_DW = 32;          // [bit], must be a power of 2 and >=8
    localparam int unsigned CUT_N_WORDS = 1024;   // must be a power of 2
    localparam int unsigned CUT_N_BITS = CUT_DW * CUT_N_WORDS;

    // Derived properties of memory array
    localparam int unsigned N_PAR_CUTS = AXI_DW / CUT_DW;
    localparam int unsigned PAR_CUTS_N_BYTES = N_PAR_CUTS * CUT_N_BITS / 8;
    localparam int unsigned N_SER_CUTS = N_BYTES / PAR_CUTS_N_BYTES;

    // Types for one memory cut
    typedef logic [$clog2(CUT_N_WORDS)-1:0] cut_addr_t;
    typedef logic [CUT_DW-1:0]              cut_data_t;
    typedef logic [CUT_DW/8-1:0]            cut_strb_t;

    // Interface from memory array to memory cuts
    localparam int unsigned WORD_IDX_OFF = $clog2(AXI_DW/8);
    localparam int unsigned WORD_IDX_WIDTH = $clog2(CUT_N_WORDS);
    localparam int unsigned ROW_IDX_OFF = WORD_IDX_OFF + WORD_IDX_WIDTH;
    localparam int unsigned ROW_IDX_WIDTH = $clog2(N_SER_CUTS);
    logic       [N_SER_CUTS-1:0]                  cut_req;
    cut_addr_t                                    cut_addr_d, cut_addr_q;
    cut_data_t  [N_SER_CUTS-1:0][N_PAR_CUTS-1:0]  cut_rdata;
    cut_data_t                  [N_PAR_CUTS-1:0]  cut_wdata;
    cut_strb_t                  [N_PAR_CUTS-1:0]  cut_be;

    assign cut_addr_d = req ? addr[ROW_IDX_OFF-1:WORD_IDX_OFF] : cut_addr_q;
    if (ROW_IDX_WIDTH > 0) begin: gen_row_idx
      logic [ROW_IDX_WIDTH-1:0]row_idx_d, row_idx_q;
      assign row_idx_d = req ? addr[ROW_IDX_OFF+:ROW_IDX_WIDTH] : row_idx_q;
      always_comb begin
        cut_req = '0;
        cut_req[row_idx_d] = req;
      end
      assign rdata = cut_rdata[row_idx_q];
      always_ff @(posedge clk_i, negedge rst_ni) begin
        if (!rst_ni) begin
          row_idx_q <= '0;
        end else begin
          row_idx_q <= row_idx_d;
        end
      end
    end else begin: gen_no_row_idx
      assign cut_req = req;
      assign rdata = cut_rdata;
    end
    assign cut_wdata = wdata;
    assign cut_be = be;

    for (genvar iRow = 0; iRow < N_SER_CUTS; iRow++) begin: gen_rows
      for (genvar iCol = 0; iCol < N_PAR_CUTS; iCol++) begin: gen_cols
        tc_sram #(
          .NumWords   ( CUT_N_WORDS ), // specify explicitly for aegis!
          .DataWidth  ( CUT_DW      ), // specify explicitly for aegis!
          .ByteWidth  ( 8           ), // specify explicitly for aegis!
          .NumPorts   ( 1           )  // specify explicitly for aegis!
        ) i_tc_sram_cut (
          .clk_i,
          .rst_ni,
          .req_i    (cut_req[iRow]),
          .we_i     (we),
          .addr_i   (cut_addr_d),
          .wdata_i  (cut_wdata[iCol]),
          .be_i     (cut_be[iCol]),
          .rdata_o  (cut_rdata[iRow][iCol])
        );
      end
    end

    `FFARN(cut_addr_q, cut_addr_d, '0, clk_i, rst_ni);
  `endif

  `FFARN(req_q, req, 1'b0, clk_i, rst_ni);

  // Validate parameters and properties.
  // pragma translate_off
  initial begin
    assert (AXI_AW > 0);
    assert (AXI_AW % (2**$clog2(AXI_AW)) == 0);
    assert (AXI_DW > 0);
    assert (AXI_DW % (2**$clog2(AXI_DW)) == 0);
    assert (N_BYTES > 0);
    assert (N_BYTES % (2**$clog2(N_BYTES)) == 0);
    assert (CUT_DW % (2**$clog2(CUT_DW)) == 0);
    assert (CUT_DW >= 8);
    assert (AXI_DW >= CUT_DW);
    assert (CUT_N_WORDS % 2**$clog2(CUT_N_WORDS) == 0);
    assert (N_BYTES % PAR_CUTS_N_BYTES == 0);
  end
  // pragma translate_on

endmodule
