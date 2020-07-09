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

// Author: Robert Balas (balasr@iis.ee.ethz.ch)

module debug_system #(
  parameter int unsigned AXI_AW = 0,
  parameter int unsigned AXI_DW = 0,
  parameter int unsigned AXI_IW = 0,
  parameter int unsigned AXI_UW = 0,

  parameter logic [31:0] JTAG_IDCODE = 32'h1,
  parameter int unsigned N_CORES = 0,
  parameter int unsigned N_CLUSTERS = 0,
  parameter logic [31:0] MAX_HARTS = 0
  // parameter int                 BusWidth        = -1
) (
  input logic  clk_i,
  input logic  rst_ni,
  input logic  test_en_i,
  output logic ndmreset_no,
  // JTAG
  input logic  jtag_tck_i,
  input logic  jtag_trst_ni,
  input logic  jtag_tdi_i,
  input logic  jtag_tms_i,
  output logic jtag_tdo_o,
  output logic jtag_tdo_en_o,
  // debug requests to core
  output logic [MAX_HARTS-1:0] core_debug_req_o,
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

  // non-debug module reset
  logic                   ndmreset;
  logic                   rst_n;
  // we assume the following hartspace:
  // logic [5:0] cluster_id = 0...N_CLUSTERS-1
  // logic [3:0] core_id = 0...N_CORES-1
  // mhartid = {21'b0, cluster_id_i[5:0], 1'b0, core_id_i[3:0]}

  // each core with hartid=x must set bit number x in SELECTABLE_HARTS
  function logic [MAX_HARTS-1:0] sel_harts();
    sel_harts = 0;
    for (logic [5:0] i = 0; i < N_CLUSTERS; i++) begin
      for (logic [3:0] j = 0; j < N_CORES; j++) begin
        sel_harts |= (1 << {32'b0, i, 1'b0, j});
      end
    end
  endfunction // sel_harts

  localparam [MAX_HARTS-1:0] SELECTABLE_HARTS = sel_harts();

  // jtag tap produces dmi commands
  dm::dmi_req_t  dmi_req;
  dm::dmi_resp_t dmi_resp;

  // debug requests to cores
  dm::hartinfo_t [MAX_HARTS-1:0] hartinfo;

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
    for (int i = 0; i < MAX_HARTS; i++)
      hartinfo[i] = RI5CY_HARTINFO;
  end

`ifndef TARGET_SYNTHESIS
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
    .rst_ni                (ndmreset_no),
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
  axi_to_mem_intf #(
    .AddrWidth (AXI_AW),
    .DataWidth (AXI_DW),
    .IdWidth   (AXI_IW),
    .UserWidth (AXI_UW),
    .NumBanks  (1),
    .BufDepth  (1)
  ) i_debug_axi_to_mem_intf (
    .clk_i,
    .rst_ni        (ndmreset_no),
    .busy_o        (),
    .slv           (dm_slave),

    .mem_req_o     (tcdm_slave_req),
    .mem_gnt_i     (tcdm_slave_gnt),
    .mem_addr_o    (tcdm_slave_addr), //TODO: wen vs we
    .mem_strb_o    (tcdm_slave_be),
    .mem_atop_o    (),
    .mem_we_o      (tcdm_slave_we),
    .mem_wdata_o   (tcdm_slave_wdata),
    .mem_rvalid_i  (tcdm_slave_r_valid),
    .mem_rdata_i   (tcdm_slave_r_rdata)
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
    .tdo_oe_o         (jtag_tdo_en_o)
  );


  // RISC-V External Debug Version 0.13.1
  dm_top #(
    .NrHarts           (MAX_HARTS),
    .BusWidth          (BUS_WIDTH),
    .SelectableHarts   (SELECTABLE_HARTS)
  ) i_dm_top (
    .clk_i,
    .rst_ni,
    .testmode_i        (test_en_i),
    .ndmreset_o        (ndmreset),
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

  always_comb begin
    rst_n = rst_ni & (~ndmreset);
    if (test_en_i) begin
      rst_n = rst_ni;
    end
  end
  // generate clean system reset signal
  rstgen i_rstgen_main (
    .clk_i        (clk_i),
    .rst_ni       (rst_n),
    .test_mode_i  (test_en_i),
    .rst_no       (ndmreset_no),
    .init_no      () // keep open
  );

endmodule // debug_system
