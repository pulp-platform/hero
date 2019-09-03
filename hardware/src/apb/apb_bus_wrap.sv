// Copyright 2019 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

// TODO: put into updated apb repo

module apb_bus_wrap #(
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
  APB_BUS.Slave   inp,
  APB_BUS.Master  oup[N_SLV-1:0]
);

  logic [N_SLV-1:0][ADDR_WIDTH-1:0]  paddr;
  logic [N_SLV-1:0]           [2:0]  pprot;
  logic [N_SLV-1:0]                  psel;
  logic [N_SLV-1:0]                  penable;
  logic [N_SLV-1:0]                  pwrite;
  logic [N_SLV-1:0][DATA_WIDTH-1:0]  pwdata;
  logic [N_SLV-1:0][STRB_WIDTH-1:0]  pstrb;
  logic [N_SLV-1:0]                  pready;
  logic [N_SLV-1:0][DATA_WIDTH-1:0]  prdata;
  logic [N_SLV-1:0]                  pslverr;

  apb_bus #(
    .ADDR_WIDTH (ADDR_WIDTH),
    .DATA_WIDTH (DATA_WIDTH),
    .N_SLV      (N_SLV),
    .ADDR_BEGIN (ADDR_BEGIN),
    .ADDR_END   (ADDR_END)
  ) i_apb_bus (
    .paddr_i    (inp.paddr),
    .pprot_i    ('0), // TODO: connect after upgrade to APBv2
    .psel_i     (inp.psel),
    .penable_i  (inp.penable),
    .pwrite_i   (inp.pwrite),
    .pwdata_i   (inp.pwdata),
    .pstrb_i    ('1), // TODO: connect after upgrade to APBv2
    .pready_o   (inp.pready),
    .prdata_o   (inp.prdata),
    .pslverr_o  (inp.pslverr),

    .paddr_o    (paddr),
    .pprot_o    (), // TODO: connect after upgrade to APBv2
    .psel_o     (psel),
    .penable_o  (penable),
    .pwrite_o   (pwrite),
    .pwdata_o   (pwdata),
    .pstrb_o    (), // TODO: connect after upgrade to APBv2
    .pready_i   (pready),
    .prdata_i   (prdata),
    .pslverr_i  (pslverr)
  );

  for (genvar i = 0; i < N_SLV; i++) begin: gen_bind_oup
    assign oup[i].paddr   = paddr[i];
    //assign oup[i].pprot   = pprot[i]; // TODO: connect after upgrade to APBv2
    assign oup[i].psel    = psel[i];
    assign oup[i].penable = penable[i];
    assign oup[i].pwrite  = pwrite[i];
    assign oup[i].pwdata  = pwdata[i];
    //assign oup[i].pstrb   = pstrb[i]; // TODO: connect after upgrade to APBv2
    assign pready[i]      = oup[i].pready;
    assign prdata[i]      = oup[i].prdata;
    assign pslverr[i]     = oup[i].pslverr;
  end

endmodule
