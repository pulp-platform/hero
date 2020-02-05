// Copyright 2019 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

// Author: Robert Balas (balasr@iis.ee.ethz.ch)

module debug_system #(
  parameter int unsigned AXI_AW = 0,
  parameter int unsigned AXI_DW = 0,
  parameter int unsigned AXI_IW = 0,
  parameter int unsigned AXI_UW = 0,

  parameter logic [31:0] JTAG_IDCODE = 32'h1,
  parameter int          NR_HARTS = -1
  // parameter int                 BusWidth        = -1,
  // parameter logic [NR_HARTS-1:0] SelectableHarts = -1,
) (
  input logic  clk_i,
  input logic  rst_ni,
  input logic  test_en_i,
  // JTAG
  input logic  jtag_tck_i,
  input logic  jtag_trst_ni,
  input logic  jtag_tdi_i,
  input logic  jtag_tms_i,
  output logic jtag_tdo_o,
  // debug requests to core
  output logic [NR_HARTS-1:0] core_debug_req_o,
  // access from cores
  AXI_BUS.Slave dm_slave,

  // debug module access to whole address space (system bus access)
  AXI_BUS.Master dm_master
);

  // can't really be changed currently
  localparam int unsigned BUS_WIDTH = 32;

  // debug module -> core2axi -> dm_master
  // nothing ...
  logic                   system_bus_req;
  logic                   system_bus_we;
  logic [BUS_WIDTH-1:0]   system_bus_addr;
  logic [BUS_WIDTH/8-1:0] system_bus_be;
  logic [BUS_WIDTH-1:0]   system_bus_wdata;
  logic                   system_bus_gnt;
  logic                   system_bus_r_valid;
  logic [BUS_WIDTH-1:0]   system_bus_r_rdata;

  // dm_slave -> axi2mem -> debug module
  logic                   tcdm_slave_req;
  logic                   tcdm_slave_we;
  logic [BUS_WIDTH-1:0]   tcdm_slave_addr;
  logic [BUS_WIDTH/8-1:0] tcdm_slave_be;
  logic [BUS_WIDTH-1:0]   tcdm_slave_wdata;
  logic                   tcdm_slave_gnt;
  logic                   tcdm_slave_r_valid;
  logic [BUS_WIDTH-1:0]   tcdm_slave_r_rdata;

  // signals between dmi and debug module
  logic                   dmi_req_valid;
  logic                   dmi_req_ready;
  logic                   dmi_resp_ready;
  logic                   dmi_resp_valid;

  // we assume a continuous hartspace where are all harts are selectable
  localparam [NR_HARTS-1:0] SELECTABLE_HARTS = '1;
  // jtag tap produces dmi commands
  dm::dmi_req_t  dmi_req;
  dm::dmi_resp_t dmi_resp;

  // // debug requests to cores
  // logic          [NR_HARTS-1:0] core_debug_req;
  // We want the harts to be numbered from 0 to NR_HARTS-1. The spec allows
  // "holes" in the hart space but tools are not able to handle these cases.
  dm::hartinfo_t [NR_HARTS-1:0] hartinfo;

  // describe capabilities of a hart
  localparam dm::hartinfo_t RI5CY_HARTINFO = '{
    zero1:      '0,
    nscratch:   2, // Debug module needs at least two scratch regs
    zero0:      '0,
    dataaccess: 1'b1, // data registers are memory mapped in the debugger
    datasize:   dm::DataCount,
    dataaddr:   dm::DataAddr
  };

  // don't try to be cute with array literals it is going to blow up in your
  // face
  always_comb begin
    hartinfo = '{default: '0};
    for (int i = 0; i < NR_HARTS; i++)
      hartinfo[i] = RI5CY_HARTINFO;
  end

`ifndef SYNTHESIS
  initial begin
    assert (AXI_DW == 32)
      else $fatal("debug module doesn't not support AXI_DW value");
    assert (AXI_AW == 32)
      else $fatal("debug module doesn't not support AXI_AW value");
  end
`endif

  // protocol conversion for the system bus access
  // debug module (tcdm) -> AXI
  assign dm_master.aw_atop = '0;

  core2axi #(
    .AXI4_ADDRESS_WIDTH (AXI_AW),
    .AXI4_RDATA_WIDTH   (AXI_DW),
    .AXI4_WDATA_WIDTH   (AXI_DW),
    .AXI4_ID_WIDTH      (AXI_IW),
    .AXI4_USER_WIDTH    (AXI_UW),
    .REGISTERED_GRANT   ("FALSE")           // "TRUE"|"FALSE"
  ) i_debug_core2axi (
    .clk_i,
    .rst_ni,
    .data_req_i            (system_bus_req),
    .data_gnt_o            (system_bus_gnt),
    .data_rvalid_o         (system_bus_r_valid),
    .data_addr_i           (system_bus_addr),
    .data_we_i             (system_bus_we),
    .data_be_i             (system_bus_be),
    .data_rdata_o          (system_bus_r_rdata),
    .data_wdata_i          (system_bus_wdata),
    // AXI write address bus
    .aw_id_o               (dm_master.aw_id),
    .aw_addr_o             (dm_master.aw_addr),
    .aw_len_o              (dm_master.aw_len),
    .aw_size_o             (dm_master.aw_size),
    .aw_burst_o            (dm_master.aw_burst),
    .aw_lock_o             (dm_master.aw_lock),
    .aw_cache_o            (dm_master.aw_cache),
    .aw_prot_o             (dm_master.aw_prot),
    .aw_region_o           (dm_master.aw_region),
    .aw_user_o             (dm_master.aw_user),
                           // TODO: dm_master.aw_atop;
    .aw_qos_o              (dm_master.aw_qos),
    .aw_valid_o            (dm_master.aw_valid),
    .aw_ready_i            (dm_master.aw_ready),
    // AXI write data bus
    .w_data_o              (dm_master.w_data),
    .w_strb_o              (dm_master.w_strb),
    .w_last_o              (dm_master.w_last),
    .w_user_o              (dm_master.w_user),
    .w_valid_o             (dm_master.w_valid),
    .w_ready_i             (dm_master.w_ready),
    // AXI write response bus
    .b_id_i                (dm_master.b_id),
    .b_resp_i              (dm_master.b_resp),
    .b_valid_i             (dm_master.b_valid),
    .b_user_i              (dm_master.b_user),
    .b_ready_o             (dm_master.b_ready),
    // AXI read address bus
    .ar_id_o               (dm_master.ar_id),
    .ar_addr_o             (dm_master.ar_addr),
    .ar_len_o              (dm_master.ar_len),
    .ar_size_o             (dm_master.ar_size),
    .ar_burst_o            (dm_master.ar_burst),
    .ar_lock_o             (dm_master.ar_lock),
    .ar_cache_o            (dm_master.ar_cache),
    .ar_prot_o             (dm_master.ar_prot),
    .ar_region_o           (dm_master.ar_region),
    .ar_user_o             (dm_master.ar_user),
    .ar_qos_o              (dm_master.ar_qos),
    .ar_valid_o            (dm_master.ar_valid),
    .ar_ready_i            (dm_master.ar_ready),
    //AXI read data bus
    .r_id_i                (dm_master.r_id),
    .r_data_i              (dm_master.r_data),
    .r_resp_i              (dm_master.r_resp),
    .r_last_i              (dm_master.r_last),
    .r_user_i              (dm_master.r_user),
    .r_valid_i             (dm_master.r_valid),
    .r_ready_o             (dm_master.r_ready)
  );

  // protocol conversion
  // AXI -> debug module (tcdm)
  axi_tcdm_if #(
    .AXI_ADDR_WIDTH       (AXI_AW),
    .AXI_DATA_WIDTH       (AXI_DW),
    .AXI_USER_WIDTH       (AXI_UW),
    .AXI_ID_WIDTH         (AXI_IW)
  ) i_debug_axi_tcdm_if (
    .clk_i,
    .rst_ni,
    .slave                 (dm_slave),

    .tcdm_master_req_o     (tcdm_slave_req),
    .tcdm_master_addr_o    (tcdm_slave_addr), //TODO: wen vs we
    .tcdm_master_we_o      (tcdm_slave_we),
    .tcdm_master_be_o      (tcdm_slave_be),
    .tcdm_master_data_o    (tcdm_slave_wdata),
    .tcdm_master_gnt_i     (tcdm_slave_gnt),

    .tcdm_master_r_valid_i (tcdm_slave_r_valid),
    .tcdm_master_r_data_i  (tcdm_slave_r_rdata)
  );


  // jtag tap and debug module
  dmi_jtag #(
    .IdcodeValue      (JTAG_IDCODE)
  ) i_dmi_jtag (
    .clk_i,
    .rst_ni,
    .testmode_i       (test_en_i),
    .dmi_req_o        (dmi_req),
    .dmi_req_valid_o  (dmi_req_valid),
    .dmi_req_ready_i  (dmi_req_ready),
    .dmi_resp_i       (dmi_resp),
    .dmi_resp_ready_o (dmi_resp_ready),
    .dmi_resp_valid_i (dmi_resp_valid),
    .dmi_rst_no       (), // TODO: global reset by dm
    .tck_i            (jtag_tck_i),
    .tms_i            (jtag_tms_i),
    .trst_ni          (jtag_trst_ni),
    .td_i             (jtag_tdi_i),
    .td_o             (jtag_tdo_o),
    .tdo_oe_o         ()
  );


  // RISC-V External Debug Version 0.13.1
  dm_top #(
    .NrHarts           (NR_HARTS),
    .BusWidth          (BUS_WIDTH),
    .SelectableHarts   (SELECTABLE_HARTS)
  ) i_dm_top (
    .clk_i,
    .rst_ni,
    .testmode_i        (test_en_i),
    .ndmreset_o        (), // TODO: allow global reset
    .dmactive_o        (), // active debug session
    .debug_req_o       (core_debug_req_o),
    .unavailable_i     (~SELECTABLE_HARTS),
    .hartinfo_i        (hartinfo),

    .slave_req_i       (tcdm_slave_req),
    .slave_we_i        (tcdm_slave_we),
    .slave_addr_i      (tcdm_slave_addr),
    .slave_be_i        (tcdm_slave_be),
    .slave_wdata_i     (tcdm_slave_wdata),
    .slave_rdata_o     (tcdm_slave_r_rdata),

    .master_req_o      (system_bus_req),
    .master_add_o      (system_bus_addr),
    .master_we_o       (system_bus_we),
    .master_wdata_o    (system_bus_wdata),
    .master_be_o       (system_bus_be),
    .master_gnt_i      (system_bus_gnt),
    .master_r_valid_i  (system_bus_r_valid),
    .master_r_rdata_i  (system_bus_r_rdata),

    .dmi_rst_ni        (rst_ni),
    .dmi_req_valid_i   (dmi_req_valid),
    .dmi_req_ready_o   (dmi_req_ready),
    .dmi_req_i         (dmi_req),
    .dmi_resp_valid_o  (dmi_resp_valid),
    .dmi_resp_ready_i  (dmi_resp_ready),
    .dmi_resp_o        (dmi_resp)
  );

  // extend tcdm_slave* to full behaviour
  assign tcdm_slave_gnt = tcdm_slave_req;
  always_ff @(posedge clk_i or negedge rst_ni) begin : dm_tcdm_valid_grant
    if(!rst_ni) begin
      tcdm_slave_r_valid <= 0;
    end else begin
      tcdm_slave_r_valid <= tcdm_slave_gnt;
    end
  end

endmodule // debug_system
