// Copyright (c) 2020 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

// Author:
// Andreas Kurth  <akurth@iis.ee.ethz.ch>

`include "axi/typedef.svh"

module hero_axi_mailbox #(
  parameter int unsigned Depth = 32'd0,
  parameter int unsigned AxiAddrWidth = 32'd0,
  parameter int unsigned AxiDataWidth = 32'd0,
  parameter int unsigned AxiIdWidth = 32'd0,
  parameter int unsigned AxiUserWidth = 32'd0,
  parameter type req_t = logic,
  parameter type rsp_t = logic,
  // Dependent parameters; DO NOT OVERRIDE!
  parameter type addr_t = logic [AxiAddrWidth-1:0]
) (
  input  logic  clk_i,
  input  logic  rst_ni,
  input  logic  test_i,
  input  req_t  host_req_i,
  output rsp_t  host_rsp_o,
  output logic  host_irq_o,
  input  addr_t host_mbox_base_addr_i,
  input  req_t  dev_req_i,
  output rsp_t  dev_rsp_o,
  output logic  dev_irq_o,
  input  addr_t dev_mbox_base_addr_i
);

  typedef logic   [AxiDataWidth-1:0] data_t;
  typedef logic [AxiDataWidth/8-1:0] strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(lite_aw_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(lite_w_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(lite_b_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(lite_ar_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(lite_r_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(lite_req_t, lite_aw_t, lite_w_t, lite_ar_t)
  `AXI_LITE_TYPEDEF_RESP_T(lite_rsp_t, lite_b_t, lite_r_t)

  lite_req_t  host_lite_req,  dev_lite_req;
  lite_rsp_t  host_lite_rsp,  dev_lite_rsp;

  axi_to_axi_lite #(
    .AxiAddrWidth     (AxiAddrWidth),
    .AxiDataWidth     (AxiDataWidth),
    .AxiIdWidth       (AxiIdWidth),
    .AxiUserWidth     (AxiUserWidth),
    .AxiMaxWriteTxns  (2),
    .AxiMaxReadTxns   (2),
    .FallThrough      (1'b1),
    .full_req_t       (req_t),
    .full_resp_t      (rsp_t),
    .lite_req_t       (lite_req_t),
    .lite_resp_t      (lite_rsp_t)
  ) i_axi_to_axi_lite_host (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_req_i  (host_req_i),
    .slv_resp_o (host_rsp_o),
    .mst_req_o  (host_lite_req),
    .mst_resp_i (host_lite_rsp)
  );
  axi_to_axi_lite #(
    .AxiAddrWidth     (AxiAddrWidth),
    .AxiDataWidth     (AxiDataWidth),
    .AxiIdWidth       (AxiIdWidth),
    .AxiUserWidth     (AxiUserWidth),
    .AxiMaxWriteTxns  (2),
    .AxiMaxReadTxns   (2),
    .FallThrough      (1'b1),
    .full_req_t       (req_t),
    .full_resp_t      (rsp_t),
    .lite_req_t       (lite_req_t),
    .lite_resp_t      (lite_rsp_t)
  ) i_axi_to_axi_lite_dev (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_req_i  (dev_req_i),
    .slv_resp_o (dev_rsp_o),
    .mst_req_o  (dev_lite_req),
    .mst_resp_i (dev_lite_rsp)
  );

  axi_lite_mailbox #(
    .MailboxDepth   ( Depth ),
    .IrqEdgeTrig    ( 1'b0  ),
    .IrqActHigh     ( 1'b1  ),
    .AxiAddrWidth   ( AxiAddrWidth  ),
    .AxiDataWidth   ( AxiDataWidth  ),
    .req_lite_t     ( lite_req_t    ),
    .resp_lite_t    ( lite_rsp_t    )
  ) i_lite_mailbox (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_reqs_i   ({dev_lite_req,         host_lite_req}),
    .slv_resps_o  ({dev_lite_rsp,         host_lite_rsp}),
    .irq_o        ({dev_irq_o,            host_irq_o}),
    .base_addr_i  ({dev_mbox_base_addr_i, host_mbox_base_addr_i})
  );

endmodule

`include "axi/assign.svh"

module hero_axi_mailbox_intf #(
  parameter int unsigned Depth = 32'd0,
  parameter int unsigned AxiAddrWidth = 32'd0,
  parameter int unsigned AxiDataWidth = 32'd0,
  parameter int unsigned AxiIdWidth = 32'd0,
  parameter int unsigned AxiUserWidth = 32'd0,
  // Dependent parameters; DO NOT OVERRIDE!
  parameter type addr_t = logic [AxiAddrWidth-1:0]
) (
  input  logic  clk_i,
  input  logic  rst_ni,
  input  logic  test_i,
  AXI_BUS.Slave host_slv,
  output logic  host_irq_o,
  input  addr_t host_mbox_base_addr_i,
  AXI_BUS.Slave dev_slv,
  output logic  dev_irq_o,
  input  addr_t dev_mbox_base_addr_i
);

  typedef logic   [AxiDataWidth-1:0] data_t;
  typedef logic [AxiDataWidth/8-1:0] strb_t;
  typedef logic     [AxiIdWidth-1:0] id_t;
  typedef logic   [AxiUserWidth-1:0] user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_t, w_t, ar_t)
  `AXI_TYPEDEF_RESP_T(rsp_t, b_t, r_t)

  req_t host_req, dev_req;
  rsp_t host_rsp, dev_rsp;
  `AXI_ASSIGN_TO_REQ(host_req, host_slv)
  `AXI_ASSIGN_TO_REQ(dev_req, dev_slv)
  `AXI_ASSIGN_FROM_RESP(host_slv, host_rsp)
  `AXI_ASSIGN_FROM_RESP(dev_slv, dev_rsp)

  hero_axi_mailbox #(
    .Depth  (Depth),
    .AxiAddrWidth (AxiAddrWidth),
    .AxiDataWidth (AxiDataWidth),
    .AxiIdWidth   (AxiIdWidth),
    .AxiUserWidth (AxiUserWidth),
    .req_t        (req_t),
    .rsp_t        (rsp_t)
  ) i_mailbox (
    .clk_i,
    .rst_ni,
    .test_i,
    .host_req_i             (host_req),
    .host_rsp_o             (host_rsp),
    .host_irq_o,
    .host_mbox_base_addr_i,
    .dev_req_i              (dev_req),
    .dev_rsp_o              (dev_rsp),
    .dev_irq_o,
    .dev_mbox_base_addr_i
  );

endmodule
