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

logic [31:0] BE_BW;
  
assign BE_BW      = { {8{be_i[3]}}, {8{be_i[2]}}, {8{be_i[1]}}, {8{be_i[0]}} };

`ifdef SYNTHESIS
              
   IN22FDX_S1D_NFRG_W04096B032M04C128  cut
     (
      .CLK          ( clk_i            ), // input
      .CEN          ( ~req_i           ), // input
      .RDWEN        ( we_i             ), // input
      .DEEPSLEEP    ( 1'b0             ), // input
      .POWERGATE    ( 1'b0             ), // input
      .AS           ( addr_i[6:4]      ), // input
      .AW           ( {addr_i[11:7],addr_i[3:2]} ), // input
      .AC           ( addr_i[1:0]      ), // input
      .D            ( wdata_i          ), // input
      .BW           ( BE_BW            ), // input
      .T_BIST       ( 1'b0             ), // input
      .T_LOGIC      ( 1'b0             ), // input
      .T_CEN        ( 1'b1             ), // input
      .T_RDWEN      ( 1'b1             ), // input
      .T_DEEPSLEEP  ( 1'b0             ), // input
      .T_POWERGATE  ( 1'b0             ), // input
      .T_AS         ( '0               ), // input
      .T_AW         ( '0               ), // input
      .T_AC         ( '0               ), // input
      .T_D          ( '0               ), // input
      .T_BW         ( '0               ), // input
      .T_WBT        ( 1'b0             ), // input
      .T_STAB       ( 1'b0             ), // input
      .MA_SAWL      ( '0               ), // input
      .MA_WL        ( '0               ), // input
      .MA_WRAS      ( '0               ), // input
      .MA_WRASD     ( 1'b0             ), // input
      .Q            ( rdata_o          ), // output
      .OBSV_CTL     (                  )  // output
      );

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
