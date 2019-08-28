// Copyright 2019 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

module soc_peripherals #(
  parameter int unsigned  AXI_AW      = 0,
  parameter int unsigned  AXI_IW      = 0,
  parameter int unsigned  AXI_UW      = 0,
  parameter int unsigned  N_CORES     = 0,
  parameter int unsigned  N_CLUSTERS  = 0
) (
  input  logic  clk_i,
  input  logic  rst_ni,

  input  logic  test_en_i,

  AXI_BUS.Slave axi
);

  localparam int unsigned APB_AW  = 32;
  localparam int unsigned APB_DW  = 32;
  localparam int unsigned AXI_DW  = 64;

  APB_BUS #(
    .APB_ADDR_WIDTH (APB_AW),
    .APB_DATA_WIDTH (APB_DW)
  ) apb ();

  axi2apb_wrap #(
    .AXI_ADDR_WIDTH   (AXI_AW),
    .AXI_DATA_WIDTH   (AXI_DW),
    .AXI_ID_WIDTH     (AXI_IW),
    .AXI_USER_WIDTH   (AXI_UW),
    .APB_ADDR_WIDTH   (APB_AW),
    .APB_DATA_WIDTH   (APB_DW)
  ) i_axi2apb (
    .clk_i,
    .rst_ni,
    .test_en_i,
    .axi_slave  (axi),
    .apb_master (apb)
  );

  APB_BUS #(
    .APB_ADDR_WIDTH (APB_AW),
    .APB_DATA_WIDTH (APB_DW)
  ) apb_periphs[1:0] ();

  apb_bus_wrap #(
    .ADDR_WIDTH (APB_AW),
    .DATA_WIDTH (APB_DW),
    .N_SLV      (2),
    .ADDR_BEGIN ({32'h1A10_4000, 32'h1A10_3000}),
    .ADDR_END   ({32'h1A10_4FFF, 32'h1A10_3FFF})
  ) i_bus (
    .inp  (apb),
    .oup  (apb_periphs)
  );

  `ifndef TARGET_SYNTHESIS
    apb_stdout #(
      .N_CORES    (N_CORES),
      .N_CLUSTERS (N_CLUSTERS),
      .ADDR_WIDTH (APB_AW),
      .DATA_WIDTH (APB_DW)
    ) i_stdout (
      .clk_i,
      .rst_ni,
      .apb  (apb_periphs[1])
    );
  `else
    assign apb_periphs[1].pready = 1'b1;
    assign apb_periphs[1].pslverr = 1'b1;
    assign apb_periphs[1].prdata = '0;
  `endif

  soc_ctrl_regs #(
    .N_CORES    (N_CORES),
    .N_CLUSTERS (N_CLUSTERS),
    .ADDR_WIDTH (APB_AW),
    .DATA_WIDTH (APB_DW)
  ) i_soc_ctrl_regs (
    .clk_i,
    .rst_ni,
    .apb    (apb_periphs[0])
  );

endmodule
