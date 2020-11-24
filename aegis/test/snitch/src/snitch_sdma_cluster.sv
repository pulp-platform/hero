/// Snitch many-core cluster with improved TCDM interconnect.

`include "common_cells/registers.svh"
`include "axi/assign.svh"

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
module snitch_sdma_cluster #(
  parameter logic [31:0] BootAddr    = 32'h0,
  parameter logic [31:0] MTVEC       = BootAddr,
  // make sure NrCores and NrBanks are aligned to powers of two at the moment
  parameter int unsigned NrCores     = 8,
  parameter int unsigned BankFactor  = 2,
  parameter bit          RVE         = 0,
  parameter bit          RVFD        = 1,
  parameter bit          SDMA        = 1,
  parameter int unsigned InstDepth   = 1024, // instruction memory size in bytes per core (in bytes)
  parameter int unsigned TCDMDepth   = 1024,  // data/TCDM memory depth per cut (in words)
  parameter tcdm_interconnect_pkg::topo_e Topology  = tcdm_interconnect_pkg::BFLY4,
  parameter int unsigned NumPar      = 1,  // number of parallel layers in
  /* Timing Tuning Parameters */
  parameter bit          RegisterAmo        = 1'b0, // Cut path between request and response at the cost of increased AMO latency (use for slow TCDM memories)
  parameter bit          RegisterOffload    = 1'b1, // Insert Pipeline registers into off-loading path (request)
  parameter bit          RegisterOffloadRsp = 1'b0, // Insert Pipeline registers into off-loading path (response)
  parameter bit          RegisterTCDMReq    = 1'b1, // Insert Pipeline registers into data memory request path
  parameter bit          RegisterTCDMCuts   = 1'b0, // Insert Pipeline registers after each memory cut
  parameter bit          RegisterExtWide    = 1'b0, // Decouple wide external AXI plug
  parameter bit          RegisterExtNarrow  = 1'b0, // Decouple narrow external AXI plug
  // memory latency parameter
  parameter int unsigned MemoryMacroLatency = 1,
  // Do Not Change:
  parameter int          CoresPerHive = 4,
  parameter int unsigned ICacheSets   = CoresPerHive, // Nr of instruction cache sets
  localparam int NrHives = NrCores / CoresPerHive
) (
  input  logic                          clk_i,
  input  logic                          rst_i, // synchronouse actve high reset
  input  logic [9:0]                    hart_base_id_i, // first id of the cluster
  input  snitch_axi_pkg::req_t          axi_slv_req_i,
  output snitch_axi_pkg::resp_t         axi_slv_res_o,
  output snitch_axi_pkg::req_slv_t      axi_mst_req_o,
  input  snitch_axi_pkg::resp_slv_t     axi_mst_res_i,
  output snitch_axi_pkg::req_dma_slv_t  ext_dma_req_o, // CAREFUL: This is the MST port!
  input  snitch_axi_pkg::resp_dma_slv_t ext_dma_resp_i // CAREFUL: This is the MST port!
);

  localparam TotNrCores = NrCores + SDMA;
  localparam TCDMAddrWidth = $clog2(TCDMDepth);
  // Two ports SSRs + BankFactor * NrCores
  localparam XSSR = 1'b1; // TODO(zarubaf): Move to parameter list
  localparam NrBanks = (XSSR ? 2 : 1) * BankFactor * NrCores;
  localparam DMADataWidth = snitch_pkg::DmaDataWidth;  // DMA data port width
  localparam BPSB = DMADataWidth / 64;                 //BPSB: banks per super bank
  localparam NrSuperBanks = NrBanks / BPSB;
  localparam NrDMAPorts = 1;

  // the last hive in the cluster can potentially be a special hive (holding the SDMA)
  // it therefore can hold a different number of cores
  localparam CoresPerSHive = CoresPerHive + SDMA;
  localparam NrTotalCores  = NrCores + SDMA;

  // Sanity check the parameters. Not every configuration makes sense.
  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assert(DMADataWidth == 512)    else $info("Design was never tested with this configuration");
    assert(DMADataWidth % 64 == 0) else $fatal(1, "DMA port has to be multiple of 64");
    assert(NrBanks > 7)            else $fatal(1, "Expect more than 8 banks");
    assert(NrBanks % 8 == 0)       else $fatal(1, "Number of Banks not divisible by 8");
    assert(CoresPerHive <= NrCores) else $fatal(1, "Can't have more cores per hive than actual cores.");
  end
  `endif
  // pragma translate_on

  logic soc_qvalid;
  logic soc_qready;
  logic soc_pvalid;
  logic soc_pready;

  logic refill_qvalid_o;
  logic refill_qready_i;
  logic refill_pvalid_i;
  logic refill_plast_i;
  logic refill_pready_o;

  // DMA AXI buses
  snitch_axi_pkg::req_dma_t      [snitch_pkg::NrDmaMasters-1:0] axi_dma_mst_req;
  snitch_axi_pkg::resp_dma_t     [snitch_pkg::NrDmaMasters-1:0] axi_dma_mst_res;
  snitch_axi_pkg::req_dma_slv_t  [snitch_pkg::NrDmaSlaves-1 :0] axi_dma_slv_req;
  snitch_axi_pkg::resp_dma_slv_t [snitch_pkg::NrDmaSlaves-1 :0] axi_dma_slv_res;

  // AXI-like read-only interface
  typedef struct packed {
      logic [31:0] addr;
      logic [7:0]  len;
      logic        write;
  } refill_req_t;

  typedef struct packed {
      logic [63:0] data;
      logic        error;
  } refill_resp_t;

  logic [NrBanks-1:0]                                 mem_cs;
  logic [NrBanks-1:0][TCDMAddrWidth-1:0]              mem_add;
  logic [NrBanks-1:0]                                 mem_wen;
  logic [NrBanks-1:0][63:0]                           mem_wdata;
  logic [NrBanks-1:0][7:0]                            mem_be;
  logic [NrBanks-1:0][63:0]                           mem_rdata;

  logic [NrBanks-1:0]                                 mem_amo_req;
  logic [NrBanks-1:0]                                 mem_amo_gnt;
  logic [NrBanks-1:0][TCDMAddrWidth-1:0]              mem_amo_add;
  logic [NrBanks-1:0]                                 mem_amo_wen;
  logic [NrBanks-1:0][63+4:0]                         mem_amo_wdata;
  logic [NrBanks-1:0][7:0]                            mem_amo_be;
  logic [NrBanks-1:0][63+4:0]                         mem_amo_rdata;

  logic [NrSuperBanks-1:0][BPSB-1:0]                     ic_req;
  logic [NrSuperBanks-1:0][BPSB-1:0]                     ic_gnt;
  logic [NrSuperBanks-1:0][BPSB-1:0][TCDMAddrWidth-1:0]  ic_add;
  logic [NrSuperBanks-1:0][BPSB-1:0][3:0]                ic_amo;
  logic [NrSuperBanks-1:0][BPSB-1:0]                     ic_wen;
  logic [NrSuperBanks-1:0][BPSB-1:0][63:0]               ic_wdata;
  logic [NrSuperBanks-1:0][BPSB-1:0][7:0]                ic_be;
  logic [NrSuperBanks-1:0][BPSB-1:0][63:0]               ic_rdata;

  logic [NrSuperBanks-1:0]                               sb_dma_req;
  logic [NrSuperBanks-1:0]                               sb_dma_gnt;
  logic [NrSuperBanks-1:0][TCDMAddrWidth-1:0]            sb_dma_add;
  logic [NrSuperBanks-1:0][3:0]                          sb_dma_amo;
  logic [NrSuperBanks-1:0]                               sb_dma_wen;
  logic [NrSuperBanks-1:0][DMADataWidth-1:0]             sb_dma_wdata;
  logic [NrSuperBanks-1:0][DMADataWidth/8-1:0]           sb_dma_be;
  logic [NrSuperBanks-1:0][DMADataWidth-1:0]             sb_dma_rdata;

  logic                                                  ext_dma_req;
  logic                                                  ext_dma_gnt;
  logic                   [63:0]                         ext_dma_add;
  logic                   [3:0]                          ext_dma_amo;
  logic                                                  ext_dma_wen;
  logic                   [DMADataWidth-1:0]             ext_dma_wdata;
  logic                   [DMADataWidth/8-1:0]           ext_dma_be;
  logic                   [DMADataWidth-1:0]             ext_dma_rdata;

  logic [NrSuperBanks-1:0][BPSB-1:0]                     amo_req;
  logic [NrSuperBanks-1:0][BPSB-1:0]                     amo_gnt;
  logic [NrSuperBanks-1:0][BPSB-1:0][TCDMAddrWidth-1:0]  amo_add;
  logic [NrSuperBanks-1:0][BPSB-1:0][3:0]                amo_amo;
  logic [NrSuperBanks-1:0][BPSB-1:0]                     amo_wen;
  logic [NrSuperBanks-1:0][BPSB-1:0][63:0]               amo_wdata;
  logic [NrSuperBanks-1:0][BPSB-1:0][7:0]                amo_be;
  logic [NrSuperBanks-1:0][BPSB-1:0][63:0]               amo_rdata;

  // logic [NrSuperBanks-1:0]                               sel_dma;
  logic [NrBanks-1:0]                                    amo_conflict;

  // DMA Ports
  logic [NrDMAPorts-1:0]          dma_req;
  logic [NrDMAPorts-1:0][31:0]    dma_add;
  logic [NrDMAPorts-1:0]          dma_wen;
  logic [NrDMAPorts-1:0][63+4:0]  dma_wdata;
  logic [NrDMAPorts-1:0][7:0]     dma_be;
  logic [NrDMAPorts-1:0]          dma_gnt;
  logic [NrDMAPorts-1:0]          dma_vld;
  logic [NrDMAPorts-1:0][63+4:0]  dma_rdata;

  // divide bus system into two parts -> one with all hives that do not
  // contain a plattform controller (frankensnitch) and one bus for the hive that can contain it.

  // bus for the normal hives
  logic [TotNrCores-1:0]               wake_up_sync;

  logic [TotNrCores-1:0][1:0]          tcdm_req;
  snitch_pkg::addr_t [TotNrCores-1:0][1:0] tcdm_add;
  logic [TotNrCores-1:0][1:0]          tcdm_wen;
  logic [TotNrCores-1:0][1:0][63+4:0]  tcdm_wdata;
  logic [TotNrCores-1:0][1:0][7:0]     tcdm_be;
  logic [TotNrCores-1:0][1:0]          tcdm_gnt;
  logic [TotNrCores-1:0][1:0]          tcdm_vld;
  logic [TotNrCores-1:0][1:0][63+4:0]  tcdm_rdata;

  snitch_pkg::addr_t [TotNrCores-1:0][1:0]    snitch_data_qaddr;
  logic [TotNrCores-1:0][1:0]          snitch_data_qwrite;
  logic [TotNrCores-1:0][1:0][3:0]     snitch_data_qamo;
  logic [TotNrCores-1:0][1:0][1:0]     snitch_data_qsize;
  logic [TotNrCores-1:0][1:0][63:0]    snitch_data_qdata;
  logic [TotNrCores-1:0][1:0][7:0]     snitch_data_qstrb;
  logic [TotNrCores-1:0][1:0]          snitch_data_qvalid;
  logic [TotNrCores-1:0][1:0]          snitch_data_qready;
  logic [TotNrCores-1:0][1:0][63:0]    snitch_data_pdata;
  logic [TotNrCores-1:0][1:0]          snitch_data_perror;
  logic [TotNrCores-1:0][1:0]          snitch_data_pvalid;
  logic [TotNrCores-1:0][1:0]          snitch_data_pready;

  snitch_pkg::dreq_t  [TotNrCores-1:0] soc_data_q;
  logic               [TotNrCores-1:0] soc_data_qvalid, soc_data_qvalid_filtered;
  logic               [TotNrCores-1:0] soc_data_qready, soc_data_qready_filtered;
  snitch_pkg::dresp_t [TotNrCores-1:0] soc_data_p;
  logic               [TotNrCores-1:0] soc_data_pvalid;
  logic               [TotNrCores-1:0] soc_data_pready;

  refill_req_t  [NrHives-1:0] refill_q;
  logic         [NrHives-1:0] refill_qvalid;
  logic         [NrHives-1:0] refill_qready;

  refill_resp_t [NrHives-1:0] refill_p;
  logic         [NrHives-1:0] refill_pvalid;
  logic         [NrHives-1:0] refill_plast;
  logic         [NrHives-1:0] refill_pready;

  // Event counter increments for the TCDM.
  localparam NrTCDMPortsCores = (NrHives * CoresPerHive + SDMA) * 2;
  typedef struct packed {
    logic [$clog2(NrTCDMPortsCores):0] inc_accessed;  // number requests going in
    logic [$clog2(NrTCDMPortsCores):0] inc_congested; // number of requests stalled due to congestion
  } tcdm_events_t;

  snitch_pkg::core_events_t [TotNrCores-1:0]   core_events;
  tcdm_events_t        tcdm_events;

  // Optionally decouple the external wide AXI master port.
  axi_cut #(
    .Bypass    ( !RegisterExtWide                  ),
    .aw_chan_t ( snitch_axi_pkg::aw_chan_dma_slv_t ),
    .w_chan_t  ( snitch_axi_pkg::w_chan_dma_t      ),
    .b_chan_t  ( snitch_axi_pkg::b_chan_dma_slv_t  ),
    .ar_chan_t ( snitch_axi_pkg::ar_chan_dma_slv_t ),
    .r_chan_t  ( snitch_axi_pkg::r_chan_dma_slv_t  ),
    .req_t     ( snitch_axi_pkg::req_dma_slv_t     ),
    .resp_t    ( snitch_axi_pkg::resp_dma_slv_t    )
  ) i_cut_ext_wide_mst (
    .clk_i      ( clk_i                               ),
    .rst_ni     ( ~rst_i                              ),
    .slv_req_i  ( axi_dma_slv_req[snitch_pkg::SoCDMA] ),
    .slv_resp_o ( axi_dma_slv_res[snitch_pkg::SoCDMA] ),
    .mst_req_o  ( ext_dma_req_o                       ),
    .mst_resp_i ( ext_dma_resp_i                      )
  );

  // x-bar connection TCDM, SDMA, and SoC
  axi_xbar #(
    .Cfg          ( snitch_cfg::dma_xbar_cfg              ),
    .slv_aw_chan_t( snitch_axi_pkg::aw_chan_dma_t         ),
    .mst_aw_chan_t( snitch_axi_pkg::aw_chan_dma_slv_t     ),
    .w_chan_t     ( snitch_axi_pkg::w_chan_dma_t          ),
    .slv_b_chan_t ( snitch_axi_pkg::b_chan_dma_t          ),
    .mst_b_chan_t ( snitch_axi_pkg::b_chan_dma_slv_t      ),
    .slv_ar_chan_t( snitch_axi_pkg::ar_chan_dma_t         ),
    .mst_ar_chan_t( snitch_axi_pkg::ar_chan_dma_slv_t     ),
    .slv_r_chan_t ( snitch_axi_pkg::r_chan_dma_t          ),
    .mst_r_chan_t ( snitch_axi_pkg::r_chan_dma_slv_t      ),
    .slv_req_t    ( snitch_axi_pkg::req_dma_t             ),
    .slv_resp_t   ( snitch_axi_pkg::resp_dma_t            ),
    .mst_req_t    ( snitch_axi_pkg::req_dma_slv_t         ),
    .mst_resp_t   ( snitch_axi_pkg::resp_dma_slv_t        ),
    .rule_t       ( axi_pkg::xbar_rule_64_t               )
  ) i_axi_dma_xbar (
    .clk_i                  ( clk_i                      ),
    .rst_ni                 ( ~rst_i                     ),
    .test_i                 ( 1'b0                       ),
    .slv_ports_req_i        ( axi_dma_mst_req            ),
    .slv_ports_resp_o       ( axi_dma_mst_res            ),
    .mst_ports_req_o        ( axi_dma_slv_req            ),
    .mst_ports_resp_i       ( axi_dma_slv_res            ),
    .addr_map_i             ( snitch_cfg::dma_xbar_rule  ),
    .en_default_mst_port_i  (  '0                        ),
    .default_mst_port_i     (  '0                        )
  );

  // connection to memory
  REQRSP_BUS #(
    .ADDR_WIDTH ( 64                         ),
    .DATA_WIDTH ( DMADataWidth               ),
    .ID_WIDTH   ( snitch_pkg::IdWidthDmaSlave )
  ) reqresp_dma_to_tcdm[NrDMAPorts-1:0](clk_i);

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( snitch_axi_pkg::DMAAddrWidth ),
    .AXI_DATA_WIDTH ( snitch_axi_pkg::DMADataWidth ),
    .AXI_ID_WIDTH   ( snitch_pkg::IdWidthDmaSlave  ),
    .AXI_USER_WIDTH ( 1                            )
  ) dma_tcdm_slave ();

  `AXI_ASSIGN_FROM_REQ(dma_tcdm_slave, axi_dma_slv_req[snitch_pkg::TCDMDMA])
  `AXI_ASSIGN_TO_RESP(axi_dma_slv_res[snitch_pkg::TCDMDMA], dma_tcdm_slave)

  axi_to_reqrsp #(
    .IN_AW     ( snitch_axi_pkg::DMAAddrWidth    ),
    .IN_DW     ( snitch_axi_pkg::DMADataWidth    ),
    .IN_IW     ( snitch_pkg::IdWidthDmaSlave      ),
    .IN_UW     ( 1                         ),
    .OUT_AW    ( 64                        ),
    .OUT_DW    ( DMADataWidth              ),
    .NUM_PORTS ( 1                         )
  ) i_dma_axi_to_tcdm (
    .clk_i,
    .rst_ni   ( ~rst_i                     ),
    .axi_i    ( dma_tcdm_slave             ),
    .reqrsp_o ( reqresp_dma_to_tcdm        )
  );

  // the data returned by the memories is always valid N cycle later
  // this is usually handled by the TCDM interconnect correctly
  // we bypass TCDM ic here -> this delay needs to be explicitly
  // calculated.
  logic [MemoryMacroLatency-1:0] ext_dma_vld;
  always_ff @(posedge clk_i) begin : proc_delay_gnt_by_one
    if (rst_i) begin
      ext_dma_vld <= '0;
    end else begin
      ext_dma_vld[0] <= ext_dma_gnt & ext_dma_req;
      // variable delay
      if (MemoryMacroLatency > 1) begin
        for (int i = 1; i < MemoryMacroLatency; i++) begin
          ext_dma_vld[i] <= ext_dma_vld[i-1];
        end
      end
    end
  end

  reqrsp_to_tcdm #(
    .AW          ( 64                         ),
    .DW          ( DMADataWidth               ),
    .IW          ( snitch_pkg::IdWidthDmaSlave)
  ) i_ext_dma_reqrsp_to_tcdm (
    .clk_i,
    .rst_ni       ( ~rst_i                              ),
    .reqrsp_i     ( reqresp_dma_to_tcdm[0]              ),
    .tcdm_add     ( ext_dma_add                         ),
    .tcdm_wen     ( ext_dma_wen                         ),
    .tcdm_wdata   ( ext_dma_wdata                       ),
    .tcdm_be      ( ext_dma_be                          ),
    .tcdm_req     ( ext_dma_req                         ),
    .tcdm_gnt     ( ext_dma_gnt                         ),
    .tcdm_r_rdata ( ext_dma_rdata                       ),
    .tcdm_r_valid ( ext_dma_vld[MemoryMacroLatency-1]   )
  );
  assign ext_dma_amo = '0;

  // external dma transfer arbiter
  snitch_dma_addr_decoder #(
    .TCDMAddrWidth      ( TCDMAddrWidth          ),
    .DMAAddrWidth       ( 64                     ),
    .BanksPerSuperbank  ( BPSB                   ),
    .NrSuperBanks       ( NrSuperBanks           ),
    .DMADataWidth       ( DMADataWidth           ),
    .MemoryLatency      ( MemoryMacroLatency     )
  ) i_snitch_dma_addr_decoder (
    .clk_i              ( clk_i                 ),
    .rst_i              ( rst_i                 ),
    .dma_req_i          ( ext_dma_req           ),
    .dma_gnt_o          ( ext_dma_gnt           ),
    .dma_add_i          ( ext_dma_add           ),
    .dma_amo_i          ( ext_dma_amo           ),
    .dma_wen_i          ( ext_dma_wen           ),
    .dma_wdata_i        ( ext_dma_wdata         ),
    .dma_be_i           ( ext_dma_be            ),
    .dma_rdata_o        ( ext_dma_rdata         ),
    .super_bank_req_o   ( sb_dma_req            ),
    .super_bank_gnt_i   ( sb_dma_gnt            ),
    .super_bank_add_o   ( sb_dma_add            ),
    .super_bank_amo_o   ( sb_dma_amo            ),
    .super_bank_wen_o   ( sb_dma_wen            ),
    .super_bank_wdata_o ( sb_dma_wdata          ),
    .super_bank_be_o    ( sb_dma_be             ),
    .super_bank_rdata_i ( sb_dma_rdata          )
  );

  // generate tcdm
  for (genvar i = 0; i < NrSuperBanks; i++) begin : tcdm_super_bank
    // wide banks (default: 512bit)
    // initial begin
    //   $display("Superbank: %d", i);
    // end

    snitch_tcdm_mux #(
      .AddrMemWidth       ( TCDMAddrWidth     ),
      .BanksPerSuperbank  ( BPSB              ),
      .DMADataWidth       ( DMADataWidth      )
    ) i_snitch_tcdm_mux (
      .clk_i          ( clk_i                 ),
      .rst_i          ( rst_i                 ),
      .ic_req_i       ( ic_req        [i]     ),
      .ic_gnt_o       ( ic_gnt        [i]     ),
      .ic_add_i       ( ic_add        [i]     ),
      .ic_amo_i       ( ic_amo        [i]     ),
      .ic_wen_i       ( ic_wen        [i]     ),
      .ic_wdata_i     ( ic_wdata      [i]     ),
      .ic_be_i        ( ic_be         [i]     ),
      .ic_rdata_o     ( ic_rdata      [i]     ),
      .dma_req_i      ( sb_dma_req    [i]     ),
      .dma_gnt_o      ( sb_dma_gnt    [i]     ),
      .dma_add_i      ( sb_dma_add    [i]     ),
      .dma_amo_i      ( sb_dma_amo    [i]     ),
      .dma_wen_i      ( sb_dma_wen    [i]     ),
      .dma_wdata_i    ( sb_dma_wdata  [i]     ),
      .dma_be_i       ( sb_dma_be     [i]     ),
      .dma_rdata_o    ( sb_dma_rdata  [i]     ),
      .amo_req_o      ( amo_req       [i]     ),
      .amo_gnt_i      ( amo_gnt       [i]     ),
      .amo_add_o      ( amo_add       [i]     ),
      .amo_amo_o      ( amo_amo       [i]     ),
      .amo_wen_o      ( amo_wen       [i]     ),
      .amo_wdata_o    ( amo_wdata     [i]     ),
      .amo_be_o       ( amo_be        [i]     ),
      .amo_rdata_i    ( amo_rdata     [i]     ),
      .sel_dma_i      ( sb_dma_req    [i]     )
    );

    // generate banks of the superbank
    for (genvar j = 0; j < BPSB; j++) begin : tcdm_bank
      localparam k = i*BPSB + j;
      tc_sram #(
        .NumWords  ( TCDMDepth ),
        .DataWidth ( 64        ),
        .ByteWidth ( 8         ),
        .NumPorts  ( 1         )
      ) i_data_mem (
        .clk_i   ( clk_i        ),
        .rst_ni  ( ~rst_i       ),
        .req_i   ( mem_cs[k]    ),
        .we_i    ( mem_wen[k]   ),
        .addr_i  ( mem_add[k]   ),
        .wdata_i ( mem_wdata[k] ),
        .be_i    ( mem_be[k]    ),
        .rdata_o ( mem_rdata[k] )
      );

      // assignments to connect the tcdm mux in front of the atomic
      // adapters
      assign ic_req        [i][j]       = mem_amo_req   [k];
      assign mem_amo_gnt   [k]          = ic_gnt        [i][j];
      assign ic_add        [i][j]       = mem_amo_add   [k];
      assign ic_wen        [i][j]       = mem_amo_wen   [k];
      assign ic_wdata      [i][j]       = mem_amo_wdata [k][63:0];
      assign ic_be         [i][j]       = mem_amo_be    [k];
      assign mem_amo_rdata [k][63:0]    = ic_rdata      [i][j];
      assign ic_amo        [i][j]       = mem_amo_wdata [k][67:64];

      logic [63:0] amo_rdata_local;

      // TODO(zarubaf): Share atomic units between mutltiple cuts
      amo_shim #(
        .AddrMemWidth   ( TCDMAddrWidth ),
        .RegisterAmo    ( RegisterAmo   )
      ) i_amo_shim (
        .clk_i,
        .rst_ni         ( ~rst_i                   ),
        .in_req_i       ( amo_req       [i][j]     ),
        .in_gnt_o       ( amo_gnt       [i][j]     ),
        .in_add_i       ( amo_add       [i][j]     ),
        .in_wen_i       ( amo_wen       [i][j]     ),
        .in_wdata_i     ( amo_wdata     [i][j]     ),
        .in_be_i        ( amo_be        [i][j]     ),
        .in_rdata_o     ( amo_rdata_local          ),
        .in_amo_i       ( amo_amo       [i][j]     ),
        .out_req_o      ( mem_cs        [k]        ),
        .out_add_o      ( mem_add       [k]        ),
        .out_wen_o      ( mem_wen       [k]        ),
        .out_wdata_o    ( mem_wdata     [k]        ),
        .out_be_o       ( mem_be        [k]        ),
        .out_rdata_i    ( mem_rdata     [k]        ),
        .dma_access_i   ( sb_dma_req    [i]        ),
        .amo_conflict_o ( amo_conflict  [k]        )
      );
      // Insert a pipeline register at the output of each SRAM.
      if (RegisterTCDMCuts) begin: gen_tcdm_cut
        `FFNR(amo_rdata     [i][j][63:0], amo_rdata_local, clk_i)
      end else begin : gen_no_tcdm_cut
        assign amo_rdata     [i][j][63:0] = amo_rdata_local;
      end
      assign mem_amo_rdata[k][67:64] = 4'b0;
    end
  end

  //                                              v SDMA core
  localparam NumTCDMIn = 2*NrCores + NrDMAPorts + 2*SDMA;
  // we need some local signals
  logic [NumTCDMIn-1:0]       tcdm_req_in;
  snitch_pkg::addr_t [NumTCDMIn-1:0] tcdm_add_in;
  logic [NumTCDMIn-1:0]       tcdm_wen_in;
  logic [NumTCDMIn-1:0][67:0] tcdm_wdata_in;
  logic [NumTCDMIn-1:0][ 7:0] tcdm_be_in;
  logic [NumTCDMIn-1:0]       tcdm_gnt_in;
  logic [NumTCDMIn-1:0]       tcdm_vld_in;
  logic [NumTCDMIn-1:0][67:0] tcdm_rdata_in;

  assign tcdm_req_in   = {dma_req,   tcdm_req  };
  assign tcdm_add_in   = {dma_add,   tcdm_add  };
  assign tcdm_wen_in   = {dma_wen,   tcdm_wen  };
  assign tcdm_wdata_in = {dma_wdata, tcdm_wdata};
  assign tcdm_be_in    = {dma_be,    tcdm_be   };
  assign {dma_gnt,   tcdm_gnt  } = tcdm_gnt_in;
  assign {dma_vld,   tcdm_vld  } = tcdm_vld_in;
  assign {dma_rdata, tcdm_rdata} = tcdm_rdata_in;

  tcdm_interconnect #(
    .NumIn        ( NumTCDMIn                          ),
    .NumOut       ( NrBanks                            ),
    .AddrWidth    ( snitch_pkg::PLEN                   ),
    // Use additional 4 bits as atomic payload
    .DataWidth    ( 64 + 4                             ),
    .BeWidth      ( 8                                  ),
    .AddrMemWidth ( TCDMAddrWidth                      ),
    .Topology     ( Topology                           ),
    .WriteRespOn  ( {{NrDMAPorts{1'b1}}, {{2*NrCores+2*SDMA}{1'b0}}} ),
    .RespLat      ( 1 + RegisterTCDMCuts               ),
    .ByteOffWidth ( $clog2(63)-3                       ),
    .NumPar       ( NumPar                             )
  ) i_tcdm_interconnect (
    .clk_i,
    .rst_ni  ( ~rst_i        ),
    .req_i   ( tcdm_req_in   ),
    .add_i   ( tcdm_add_in   ),
    .wen_i   ( tcdm_wen_in   ),
    .wdata_i ( tcdm_wdata_in ),
    .be_i    ( tcdm_be_in    ),
    .gnt_o   ( tcdm_gnt_in   ),
    .vld_o   ( tcdm_vld_in   ),
    .rdata_o ( tcdm_rdata_in ),

    .req_o   ( mem_amo_req   ),
    .gnt_i   ( mem_amo_gnt   ),
    .add_o   ( mem_amo_add   ),
    .wen_o   ( mem_amo_wen   ),
    .wdata_o ( mem_amo_wdata ),
    .be_o    ( mem_amo_be    ),
    .rdata_i ( mem_amo_rdata )
  );

  logic [NrTCDMPortsCores-1:0] flat_acc, flat_con;

  // TCDM event counters
  `FFSR(flat_acc, tcdm_req, '0, clk_i, rst_i)
  `FFSR(flat_con, tcdm_req & ~tcdm_gnt, '0, clk_i, rst_i)

  popcount #(
    .INPUT_WIDTH ( NrTCDMPortsCores )
  ) i_popcount_req (
    .data_i      ( flat_acc                  ),
    .popcount_o  ( tcdm_events.inc_accessed  )
  );

  popcount #(
    .INPUT_WIDTH ( NrTCDMPortsCores )
  ) i_popcount_con (
    .data_i      ( flat_con                  ),
    .popcount_o  ( tcdm_events.inc_congested )
  );

  for (genvar i = 0; i < NrHives; i++) begin : gen_snitch_hive
      localparam IsLastHive = (i == (NrHives - 1));
      localparam CurrentCoresPerHive = IsLastHive ? CoresPerHive + SDMA : CoresPerHive;
      localparam idx_l = i * CoresPerHive;
      localparam idx_h = idx_l + CurrentCoresPerHive;

      for (genvar j = 0; j < CurrentCoresPerHive; j++) begin : gen_hive_ports
        localparam idx = idx_l + j;

        for (genvar k = 0; k < 2; k++) begin : gen_ports
          snitch_pkg::addr_t soc_qaddr_tmp;
          logic        soc_qwrite_tmp;
          logic [3:0]  soc_qamo_tmp;
          logic [63:0] soc_qdata_tmp;
          logic [7:0]  soc_qstrb_tmp;
          logic [1:0]  soc_qsize_tmp;
          logic        soc_qvalid_tmp;
          logic        soc_qready_tmp;
          logic [63:0] soc_pdata_tmp;
          logic        soc_perror_tmp;
          logic        soc_pvalid_tmp;
          logic        soc_pready_tmp;

          tcdm_shim #(
            .AddrWidth ( snitch_pkg::PLEN  ),
            .DataWidth ( 64       ),
            .InclDemux ( (k == 0) )
          ) i_tcdm_shim (
            .clk_i                                         ,
            .rst_i                                         ,
            .tcdm_req_o    ( tcdm_req           [idx][k] ),
            .tcdm_add_o    ( tcdm_add           [idx][k] ),
            .tcdm_wen_o    ( tcdm_wen           [idx][k] ),
            .tcdm_wdata_o  ( tcdm_wdata         [idx][k] ),
            .tcdm_be_o     ( tcdm_be            [idx][k] ),
            .tcdm_gnt_i    ( tcdm_gnt           [idx][k] ),
            .tcdm_vld_i    ( tcdm_vld           [idx][k] ),
            .tcdm_rdata_i  ( tcdm_rdata         [idx][k] ),
            .soc_qaddr_o   ( soc_qaddr_tmp                ),
            .soc_qwrite_o  ( soc_qwrite_tmp               ),
            .soc_qamo_o    ( soc_qamo_tmp                 ),
            .soc_qdata_o   ( soc_qdata_tmp                ),
            .soc_qsize_o   ( soc_qsize_tmp                ),
            .soc_qstrb_o   ( soc_qstrb_tmp                ),
            .soc_qvalid_o  ( soc_qvalid_tmp               ),
            .soc_qready_i  ( soc_qready_tmp               ),
            .soc_pdata_i   ( soc_pdata_tmp                ),
            .soc_perror_i  ( soc_perror_tmp               ),
            .soc_pvalid_i  ( soc_pvalid_tmp               ),
            .soc_pready_o  ( soc_pready_tmp               ),
            .data_qaddr_i  ( snitch_data_qaddr  [idx][k] ),
            .data_qwrite_i ( snitch_data_qwrite [idx][k] ),
            .data_qamo_i   ( snitch_data_qamo   [idx][k] ),
            .data_qdata_i  ( snitch_data_qdata  [idx][k] ),
            .data_qsize_i  ( snitch_data_qsize  [idx][k] ),
            .data_qstrb_i  ( snitch_data_qstrb  [idx][k] ),
            .data_qvalid_i ( snitch_data_qvalid [idx][k] ),
            .data_qready_o ( snitch_data_qready [idx][k] ),
            .data_pdata_o  ( snitch_data_pdata  [idx][k] ),
            .data_perror_o ( snitch_data_perror [idx][k] ),
            .data_pvalid_o ( snitch_data_pvalid [idx][k] ),
            .data_pready_i ( snitch_data_pready [idx][k] )
          );
          // Don't hook-up SSR ports
          if (k == 0) begin
            assign soc_data_q[idx].addr = soc_qaddr_tmp;
            assign soc_data_q[idx].write = soc_qwrite_tmp;
            assign soc_data_q[idx].amo = soc_qamo_tmp;
            assign soc_data_q[idx].data = soc_qdata_tmp;
            assign soc_data_q[idx].size = soc_qsize_tmp;
            assign soc_data_q[idx].strb = soc_qstrb_tmp;
            assign soc_data_qvalid[idx] = soc_qvalid_tmp;
            assign soc_qready_tmp = soc_data_qready[idx];
            assign soc_pdata_tmp = soc_data_p[idx].data;
            assign soc_perror_tmp = soc_data_p[idx].error;
            assign soc_pvalid_tmp = soc_data_pvalid[idx];
            assign soc_data_pready[idx] = soc_pready_tmp;
          // that hopefully optimizes away the logic
          end else if (k == 1) begin
            assign soc_qready_tmp = '0;
            assign soc_pdata_tmp = '0;
            assign soc_perror_tmp = '0;
            assign soc_pvalid_tmp = '0;
          end
        end
      end

      snitch_axi_pkg::req_dma_t   axi_dma_req;
      snitch_axi_pkg::resp_dma_t  axi_dma_res;

      snitch_hive #(
        .CoreCount          ( CurrentCoresPerHive      ),
        .SDMA               ( IsLastHive && SDMA       ),
        .BootAddr           ( BootAddr                 ),
        .MTVEC              ( MTVEC                    ),
        .RVE                ( RVE                      ),
        .RVFD               ( RVFD                     ),
        .RegisterOffload    ( RegisterOffload          ),
        .RegisterOffloadRsp ( RegisterOffloadRsp       ),
        .RegisterTCDMReq    ( RegisterTCDMReq          ),
        .ICacheSizeByte     ( InstDepth * CoresPerHive ),
        .ICacheSets         ( ICacheSets               )
      ) i_snitch_compute_hive (
        .clk_i                                                 ,
        .rst_i                                                 ,
        .hart_base_id_i  ( hart_base_id_i +  idx_l            ),
        .data_qaddr_o    ( snitch_data_qaddr  [idx_h-1:idx_l] ),
        .data_qwrite_o   ( snitch_data_qwrite [idx_h-1:idx_l] ),
        .data_qamo_o     ( snitch_data_qamo   [idx_h-1:idx_l] ),
        .data_qdata_o    ( snitch_data_qdata  [idx_h-1:idx_l] ),
        .data_qsize_o    ( snitch_data_qsize  [idx_h-1:idx_l] ),
        .data_qstrb_o    ( snitch_data_qstrb  [idx_h-1:idx_l] ),
        .data_qvalid_o   ( snitch_data_qvalid [idx_h-1:idx_l] ),
        .data_qready_i   ( snitch_data_qready [idx_h-1:idx_l] ),
        .data_pdata_i    ( snitch_data_pdata  [idx_h-1:idx_l] ),
        .data_perror_i   ( snitch_data_perror [idx_h-1:idx_l] ),
        .data_pvalid_i   ( snitch_data_pvalid [idx_h-1:idx_l] ),
        .data_pready_o   ( snitch_data_pready [idx_h-1:idx_l] ),
        .wake_up_sync_i  ( wake_up_sync       [idx_h-1:idx_l] ),
        .refill_qaddr_o  ( refill_q[i].addr                   ),
        .refill_qlen_o   ( refill_q[i].len                    ),
        .refill_qvalid_o ( refill_qvalid      [i]             ),
        .refill_qready_i ( refill_qready      [i]             ),
        .refill_pdata_i  ( refill_p[i].data                   ),
        .refill_perror_i ( refill_p[i].error                  ),
        .refill_pvalid_i ( refill_pvalid      [i]             ),
        .refill_plast_i  ( refill_plast       [i]             ),
        .refill_pready_o ( refill_pready      [i]             ),
        .axi_dma_req_o   ( axi_dma_req                        ),
        .axi_dma_res_i   ( axi_dma_res                        ),
        .axi_dma_busy_o  (                                    ),
        .core_events_o   ( core_events        [idx_h-1:idx_l] ),
        .axi_dma_perf_o  (                                    )
      );

      assign refill_q[i].write = 1'b0;

      if (IsLastHive && SDMA) begin : gen_dma_connection
        assign axi_dma_mst_req[snitch_pkg::SDMAMst] = axi_dma_req;
        assign axi_dma_res = axi_dma_mst_res[snitch_pkg::SDMAMst];
      end
  end

  refill_req_t refill_req_o;
  refill_resp_t refill_resp_i;

  snitch_demux #(
    .NrPorts ( NrHives       ),
    .req_t   ( refill_req_t  ),
    .resp_t  ( refill_resp_t )
  ) i_snitch_demux_refill (
    .clk_i,
    .rst_ni         ( ~rst_i          ),
    .req_payload_i  ( refill_q        ),
    .req_valid_i    ( refill_qvalid   ),
    .req_ready_o    ( refill_qready   ),
    .resp_payload_o ( refill_p        ),
    .resp_last_o    ( refill_plast    ),
    .resp_valid_o   ( refill_pvalid   ),
    .resp_ready_i   ( refill_pready   ),
    .req_payload_o  ( refill_req_o    ),
    .req_valid_o    ( refill_qvalid_o ),
    .req_ready_i    ( refill_qready_i ),
    .resp_payload_i ( refill_resp_i   ),
    .resp_last_i    ( refill_plast_i  ),
    .resp_valid_i   ( refill_pvalid_i ),
    .resp_ready_o   ( refill_pready_o )
  );

  snitch_pkg::dreq_t soc_req_o;
  snitch_pkg::dresp_t soc_resp_i;

  // need some local signals
  snitch_pkg::dreq_t [NrTotalCores-1:0] in_payload_barrier;
  logic              [NrTotalCores-1:0] in_valid_barrier;
  logic              [NrTotalCores-1:0] in_ready_barrier;
  logic              [NrTotalCores-1:0] out_valid_barrier;
  logic              [NrTotalCores-1:0] out_ready_barrier;

  assign in_payload_barrier         = soc_data_q;
  assign in_valid_barrier           = soc_data_qvalid;
  assign soc_data_qready          = in_ready_barrier;
  assign soc_data_qvalid_filtered = out_valid_barrier;
  assign out_ready_barrier          = soc_data_qready_filtered;

  snitch_barrier #(
    .NrPorts ( NrTotalCores        ),
    .req_t   ( snitch_pkg::dreq_t  )
  ) i_snitch_barrier (
    .clk_i,
    .rst_i,
    .in_payload_i ( in_payload_barrier   ),
    .in_valid_i   ( in_valid_barrier     ),
    .in_ready_o   ( in_ready_barrier     ),
    .out_valid_o  ( out_valid_barrier    ),
    .out_ready_i  ( out_ready_barrier    )
  );

  // need some local signals
  snitch_pkg::dreq_t  [NrTotalCores-1:0] req_payload_demux;
  logic               [NrTotalCores-1:0] req_valid_demux;
  logic               [NrTotalCores-1:0] req_ready_demux;
  snitch_pkg::dresp_t [NrTotalCores-1:0] resp_payload_demux;
  logic               [NrTotalCores-1:0] resp_valid_demux;
  logic               [NrTotalCores-1:0] resp_ready_demux;

  assign req_payload_demux          = soc_data_q;
  assign req_valid_demux            = soc_data_qvalid_filtered;
  assign soc_data_qready_filtered = req_ready_demux;
  assign soc_data_p               = resp_payload_demux;
  assign soc_data_pvalid          = resp_valid_demux;
  assign resp_ready_demux           = soc_data_pready;

  snitch_demux #(
    .NrPorts ( NrTotalCores        ),
    .req_t   ( snitch_pkg::dreq_t  ),
    .resp_t  ( snitch_pkg::dresp_t )
  ) i_snitch_demux_data (
    .clk_i,
    .rst_ni         ( ~rst_i               ),
    .req_payload_i  ( req_payload_demux    ),
    .req_valid_i    ( req_valid_demux      ),
    .req_ready_o    ( req_ready_demux      ),
    .resp_payload_o ( resp_payload_demux   ),
    .resp_last_o    ( ),
    .resp_valid_o   ( resp_valid_demux     ),
    .resp_ready_i   ( resp_ready_demux     ),

    .req_payload_o  ( soc_req_o            ),
    .req_valid_o    ( soc_qvalid           ),
    .req_ready_i    ( soc_qready           ),
    .resp_payload_i ( soc_resp_i           ),
    .resp_last_i    ( 1'b1                 ),
    .resp_valid_i   ( soc_pvalid           ),
    .resp_ready_o   ( soc_pready           )
  );

  snitch_axi_pkg::req_slv_t  [snitch_pkg::NrSlaves-1:0] slave_req;
  snitch_axi_pkg::resp_slv_t [snitch_pkg::NrSlaves-1:0] slave_resp;

  snitch_axi_pkg::req_t  [snitch_pkg::NrMasters-1:0] master_req;
  snitch_axi_pkg::resp_t [snitch_pkg::NrMasters-1:0] master_resp;

  snitch_axi_pkg::req_t  axi_mst_cut_req;
  snitch_axi_pkg::resp_t axi_mst_cut_resp;

  axi_xbar #(
    .Cfg           ( snitch_cfg::CLUSTER_XBAR_CFG  ),
    .slv_aw_chan_t ( snitch_axi_pkg::aw_chan_t     ),
    .mst_aw_chan_t ( snitch_axi_pkg::aw_chan_slv_t ),
    .w_chan_t      ( snitch_axi_pkg::w_chan_t      ),
    .slv_b_chan_t  ( snitch_axi_pkg::b_chan_t      ),
    .mst_b_chan_t  ( snitch_axi_pkg::b_chan_slv_t  ),
    .slv_ar_chan_t ( snitch_axi_pkg::ar_chan_t     ),
    .mst_ar_chan_t ( snitch_axi_pkg::ar_chan_slv_t ),
    .slv_r_chan_t  ( snitch_axi_pkg::r_chan_t      ),
    .mst_r_chan_t  ( snitch_axi_pkg::r_chan_slv_t  ),
    .slv_req_t     ( snitch_axi_pkg::req_t         ),
    .slv_resp_t    ( snitch_axi_pkg::resp_t        ),
    .mst_req_t     ( snitch_axi_pkg::req_slv_t     ),
    .mst_resp_t    ( snitch_axi_pkg::resp_slv_t    ),
    .rule_t        ( axi_pkg::xbar_rule_64_t       )
  ) i_cluster_xbar (
    .clk_i,
    .rst_ni                ( ~rst_i                         ),
    .test_i                ( 1'b0                           ),
    .slv_ports_req_i       ( master_req                     ),
    .slv_ports_resp_o      ( master_resp                    ),
    .mst_ports_req_o       ( slave_req                      ),
    .mst_ports_resp_i      ( slave_resp                     ),
    .addr_map_i            ( snitch_cfg::CLUSTER_XBAR_RULES ),
    .en_default_mst_port_i ( '0                             ),
    .default_mst_port_i    ( '0                             )
  );

  // Optionally decouple the external narrow AXI slave port.
  axi_cut #(
    .Bypass    ( !RegisterExtNarrow        ),
    .aw_chan_t ( snitch_axi_pkg::aw_chan_t ),
    .w_chan_t  ( snitch_axi_pkg::w_chan_t  ),
    .b_chan_t  ( snitch_axi_pkg::b_chan_t  ),
    .ar_chan_t ( snitch_axi_pkg::ar_chan_t ),
    .r_chan_t  ( snitch_axi_pkg::r_chan_t  ),
    .req_t     ( snitch_axi_pkg::req_t     ),
    .resp_t    ( snitch_axi_pkg::resp_t    )
  ) i_cut_ext_narrow_slv (
    .clk_i      ( clk_i                           ),
    .rst_ni     ( ~rst_i                          ),
    .slv_req_i  ( axi_mst_cut_req                 ),
    .slv_resp_o ( axi_mst_cut_resp                ),
    .mst_req_o  ( master_req[snitch_pkg::AXISoC]  ),
    .mst_resp_i ( master_resp[snitch_pkg::AXISoC] )
  );

  // Masters
  // Truncate address bits.
  always_comb begin
    axi_mst_cut_req = axi_slv_req_i;
    axi_mst_cut_req.aw.atop = '0;
    axi_mst_cut_req.aw.addr = '0;
    axi_mst_cut_req.ar.addr = '0;
    axi_mst_cut_req.aw.addr = snitch_cfg::TCDMStartAddress + axi_slv_req_i.aw.addr[snitch_cfg::SoCRequestAddrBits-1:0];
    axi_mst_cut_req.ar.addr = snitch_cfg::TCDMStartAddress + axi_slv_req_i.ar.addr[snitch_cfg::SoCRequestAddrBits-1:0];
    axi_slv_res_o = axi_mst_cut_resp;
  end

  // Core request
  logic [snitch_axi_pkg::AddrWidth-1:0] ze_soc_req_o_add, ze_refill_req_o_addr;
  // zero extend addresses to `snitch_axi_pkg::AddrWidth` coming from each hive.
  always_comb begin
    ze_soc_req_o_add = '0;
    ze_refill_req_o_addr = '0;
    ze_soc_req_o_add = soc_req_o.addr;
    ze_refill_req_o_addr = refill_req_o.addr;
  end
  snitch_axi_adapter #(
    .addr_t  ( snitch_axi_pkg::addr_t    ),
    .data_t  ( snitch_axi_pkg::data_t    ),
    .strb_t  ( snitch_axi_pkg::strb_t    ),
    .axi_mst_req_t  ( snitch_axi_pkg::req_t     ),
    .axi_mst_resp_t ( snitch_axi_pkg::resp_t    )
  ) i_snitch_core_axi_adapter (
    .clk_i,
    .rst_ni       ( ~rst_i            ),
    // zero extend to 64 bit
    .slv_qaddr_i  ( ze_soc_req_o_add  ),
    .slv_qwrite_i ( soc_req_o.write   ),
    .slv_qamo_i   ( soc_req_o.amo     ),
    .slv_qdata_i  ( soc_req_o.data    ),
    .slv_qstrb_i  ( soc_req_o.strb    ),
    .slv_qsize_i  ( soc_req_o.size    ),
    .slv_qrlen_i  ( '0                ),
    .slv_qvalid_i ( soc_qvalid        ),
    .slv_qready_o ( soc_qready        ),
    .slv_pdata_o  ( soc_resp_i.data   ),
    .slv_perror_o ( soc_resp_i.error  ),
    .slv_plast_o  (                   ),
    .slv_pvalid_o ( soc_pvalid        ),
    .slv_pready_i ( soc_pready        ),
    .axi_req_o    ( master_req[snitch_pkg::CoreReq]  ),
    .axi_resp_i   ( master_resp[snitch_pkg::CoreReq] )
  );

  // Instruction refill request
  snitch_axi_adapter #(
    .addr_t  ( snitch_axi_pkg::addr_t    ),
    .data_t  ( snitch_axi_pkg::data_t    ),
    .strb_t  ( snitch_axi_pkg::strb_t    ),
    .axi_mst_req_t  ( snitch_axi_pkg::req_t     ),
    .axi_mst_resp_t ( snitch_axi_pkg::resp_t    )
  ) i_snitch_refill_axi_adapter (
    .clk_i,
    .rst_ni       ( ~rst_i              ),
    .slv_qaddr_i  ( ze_refill_req_o_addr),
    .slv_qwrite_i ( '0                  ),
    .slv_qamo_i   ( '0                  ),
    .slv_qdata_i  ( '0                  ),
    .slv_qstrb_i  ( '0                  ),
    .slv_qsize_i  ( 2'b11               ),
    .slv_qrlen_i  ( refill_req_o.len    ),
    .slv_qvalid_i ( refill_qvalid_o     ),
    .slv_qready_o ( refill_qready_i     ),
    .slv_pdata_o  ( refill_resp_i.data  ),
    .slv_perror_o ( refill_resp_i.error ),
    .slv_plast_o  ( refill_plast_i      ),
    .slv_pvalid_o ( refill_pvalid_i     ),
    .slv_pready_i ( refill_pready_o     ),
    .axi_req_o    ( master_req[snitch_pkg::ICache]  ),
    .axi_resp_i   ( master_resp[snitch_pkg::ICache] )
  );

  // ---------
  // Slaves
  // ---------
  // 1. TCDM
  // Add an adapter that allows access from AXI to the TCDM. The adapter
  // translates to a request/response interface, which needs to be further
  // adapted to the TCDM, which does not support response stalls.
  REQRSP_BUS #(
    .ADDR_WIDTH ( snitch_axi_pkg::AddrWidth ),
    .DATA_WIDTH ( snitch_axi_pkg::DataWidth ),
    .ID_WIDTH   ( snitch_pkg::IdWidthSlave )
  ) axi_to_tcdm[NrDMAPorts-1:0](clk_i);

  // TODO: Remove interface
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( snitch_axi_pkg::AddrWidth ),
    .AXI_DATA_WIDTH ( snitch_axi_pkg::DataWidth ),
    .AXI_ID_WIDTH   ( snitch_pkg::IdWidthSlave  ),
    .AXI_USER_WIDTH ( snitch_axi_pkg::UserWidth )
  ) tcdm_slave ();

  `AXI_ASSIGN_FROM_REQ(tcdm_slave, slave_req[snitch_pkg::TCDM])
  `AXI_ASSIGN_TO_RESP(slave_resp[snitch_pkg::TCDM], tcdm_slave)

  axi_to_reqrsp #(
    .IN_AW     ( snitch_axi_pkg::AddrWidth ),
    .IN_DW     ( snitch_axi_pkg::DataWidth ),
    .IN_IW     ( snitch_pkg::IdWidthSlave  ),
    .IN_UW     ( snitch_axi_pkg::UserWidth ),
    .OUT_AW    ( snitch_axi_pkg::AddrWidth ),
    .OUT_DW    ( snitch_axi_pkg::DataWidth ),
    .NUM_PORTS ( NrDMAPorts                )
  ) i_axi_to_tcdm (
    .clk_i,
    .rst_ni   ( ~rst_i      ),
    .axi_i    ( tcdm_slave  ),
    .reqrsp_o ( axi_to_tcdm )
  );

  for (genvar i = 0; i < NrDMAPorts; i++) begin : gen_axi_to_tcdm_adapter
    logic [63:0] dma_add_local;
    reqrsp_to_tcdm #(
      .AW          ( snitch_axi_pkg::AddrWidth ),
      .DW          ( snitch_axi_pkg::DataWidth ),
      .IW          ( snitch_pkg::IdWidthSlave )
    ) i_reqrsp_to_tcdm (
      .clk_i,
      .rst_ni       ( ~rst_i             ),
      .reqrsp_i     ( axi_to_tcdm[i]     ),
      .tcdm_add     ( dma_add_local      ),
      .tcdm_wen     ( dma_wen[i]         ),
      .tcdm_wdata   ( dma_wdata[i][63:0] ),
      .tcdm_be      ( dma_be[i]          ),
      .tcdm_req     ( dma_req[i]         ),
      .tcdm_gnt     ( dma_gnt[i]         ),
      .tcdm_r_rdata ( dma_rdata[i][63:0] ),
      .tcdm_r_valid ( dma_vld[i]         )
    );
    assign dma_wdata[i][63+4:64] = '0;
    // truncate to physical length
    assign dma_add[i] = dma_add_local[snitch_pkg::PLEN-1:0];
  end

  // 2. Peripherals
  // TODO: Remove interface
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( snitch_axi_pkg::AddrWidth ),
    .AXI_DATA_WIDTH ( snitch_axi_pkg::DataWidth ),
    .AXI_ID_WIDTH   ( snitch_pkg::IdWidthSlave  ),
    .AXI_USER_WIDTH ( snitch_axi_pkg::UserWidth )
  ) peripheral_slave ();

  `AXI_ASSIGN_FROM_REQ(peripheral_slave, slave_req[snitch_pkg::ClusterPeripherals])
  `AXI_ASSIGN_TO_RESP(slave_resp[snitch_pkg::ClusterPeripherals], peripheral_slave)

  REG_BUS #(
    .ADDR_WIDTH (snitch_axi_pkg::AddrWidth),
    .DATA_WIDTH (snitch_axi_pkg::DataWidth)
  ) reg_bus(clk_i);

  axi_to_reg #(
    .ADDR_WIDTH ( snitch_axi_pkg::AddrWidth ),
    .DATA_WIDTH ( snitch_axi_pkg::DataWidth ),
    .DECOUPLE_W ( 1                         ),
    .ID_WIDTH   ( snitch_pkg::IdWidthSlave  ),
    .USER_WIDTH ( snitch_axi_pkg::UserWidth )
  ) i_axi_to_reg (
    .clk_i      ( clk_i            ),
    .rst_ni     ( ~rst_i           ),
    .testmode_i ( 1'b0             ),
    .in         ( peripheral_slave ),
    .reg_o      ( reg_bus          )
  );

  // local signals
  logic [NrTotalCores-1:0] wake_up_cluster;
  snitch_pkg::core_events_t [NrTotalCores-1:0] core_events_cluster;

  assign wake_up_sync = wake_up_cluster;
  assign core_events_cluster = core_events;

  snitch_cluster_peripheral #(
    .TCDMStartAddress ( snitch_cfg::TCDMStartAddress                           ),
    .TCDMEndAddress   ( snitch_cfg::TCDMStartAddress + TCDMDepth * NrBanks * 8 ),
    .tcdm_events_t    ( tcdm_events_t                                          ),
    .NrCores          ( NrTotalCores                                           )
  ) i_snitch_cluster_peripheral (
    .clk_i,
    .rst_i,
    .addr_i               ( reg_bus.addr         ),
    .wdata_i              ( reg_bus.wdata        ),
    .wstrb_i              ( reg_bus.wstrb        ),
    .write_i              ( reg_bus.write        ),
    .rdata_o              ( reg_bus.rdata        ),
    .error_o              ( reg_bus.error        ),
    .valid_i              ( reg_bus.valid        ),
    .ready_o              ( reg_bus.ready        ),
    .wake_up_o            ( wake_up_cluster      ),
    .cluster_hart_base_id_i ( hart_base_id_i       ),
    .core_events_i        ( core_events_cluster  ),
    .tcdm_events_i        ( tcdm_events          )
  );

  // Optionally decouple the external narrow AXI master ports.
  axi_cut #(
    .Bypass    ( !RegisterExtNarrow            ),
    .aw_chan_t ( snitch_axi_pkg::aw_chan_slv_t ),
    .w_chan_t  ( snitch_axi_pkg::w_chan_t      ),
    .b_chan_t  ( snitch_axi_pkg::b_chan_slv_t  ),
    .ar_chan_t ( snitch_axi_pkg::ar_chan_slv_t ),
    .r_chan_t  ( snitch_axi_pkg::r_chan_slv_t  ),
    .req_t     ( snitch_axi_pkg::req_slv_t     ),
    .resp_t    ( snitch_axi_pkg::resp_slv_t    )
  ) i_cut_ext_narrow_mst (
    .clk_i      ( clk_i                       ),
    .rst_ni     ( ~rst_i                      ),
    .slv_req_i  ( slave_req[snitch_pkg::SoC]  ),
    .slv_resp_o ( slave_resp[snitch_pkg::SoC] ),
    .mst_req_o  ( axi_mst_req_o               ),
    .mst_resp_i ( axi_mst_res_i               )
  );
endmodule


module snitch_barrier #(
  parameter int NrPorts = 0,
  parameter type req_t = logic
) (
  input  logic clk_i,
  input  logic rst_i,
  input  req_t [NrPorts-1:0] in_payload_i,
  input  logic [NrPorts-1:0] in_valid_i,
  output logic [NrPorts-1:0] in_ready_o,
  output logic [NrPorts-1:0] out_valid_o,
  input  logic [NrPorts-1:0] out_ready_i
);

  typedef enum logic [1:0] {
    Idle,
    Wait,
    Take
  } barrier_state_e;
  barrier_state_e [NrPorts-1:0] state_d, state_q;
  logic [NrPorts-1:0] is_barrier;
  logic take_barrier;

  assign take_barrier = &is_barrier;

  always_comb begin
    state_d     = state_q;
    is_barrier  = '0;
    out_valid_o = in_valid_i;
    in_ready_o  = out_ready_i;

    for (int i = 0; i < NrPorts; i++) begin
      case (state_q[i])
        Idle: begin
          if (in_valid_i[i] && (in_payload_i[i].addr == snitch_cfg::ClusterPeriphStartAddress + snitch_pkg::BarrierReg)) begin
            state_d[i] = Wait;
            out_valid_o[i] = 0;
            in_ready_o[i]  = 0;
          end
        end
        Wait: begin
          is_barrier[i]  = 1;
          out_valid_o[i] = 0;
          in_ready_o[i]  = 0;
          if (take_barrier) state_d[i] = Take;
        end
        Take: begin
          if (out_valid_o[i] && in_ready_o[i]) state_d[i] = Idle;
        end
        default: state_d[i] = Idle;
      endcase
    end
  end

  for (genvar i = 0; i < NrPorts; i++) begin : gen_ff
    `FFSR(state_q[i], state_d[i], Idle, clk_i, rst_i)
  end

endmodule


// legacy definition of the cluster. it is strongly suggested to use the
// 'snictch_sdma_cluster' for new designs.

module snitch_cluster #(
  parameter logic [31:0] BootAddr    = 32'h0,
  parameter logic [31:0] MTVEC       = BootAddr,
  // make sure NrCores and NrBanks are aligned to powers of two at the moment
  parameter int unsigned NrCores     = 16,
  parameter int unsigned BankFactor  = 2,
  parameter bit          RVE         = 0,
  parameter bit          RVFD        = 1,
  parameter int unsigned InstDepth   = 1024, // instruction memory size in bytes per core (in bytes)
  parameter int unsigned TCDMDepth   = 1024,  // data/TCDM memory depth per cut (in words)
  parameter tcdm_interconnect_pkg::topo_e Topology  = tcdm_interconnect_pkg::BFLY4,
  parameter int unsigned NumPar      = 1,  // number of parallel layers in
  /* Timing Tuning Parameters */
  parameter bit          RegisterAmo        = 1'b0, // Cut path between request and response at the cost of increased AMO latency (use for slow TCDM memories)
  parameter bit          RegisterOffload    = 1'b1, // Insert Pipeline registers into off-loading path (request)
  parameter bit          RegisterOffloadRsp = 1'b0, // Insert Pipeline registers into off-loading path (response)
  parameter bit          RegisterTCDMReq    = 1'b1, // Insert Pipeline registers into data memory request path
  // Do Not Change:
  parameter int          CoresPerHive = 4,
  parameter int unsigned ICacheSets   = CoresPerHive, // Nr of instruction cache sets
  localparam int NrHives = NrCores / CoresPerHive
) (
  input  logic                       clk_i,
  input  logic                       rst_i, // synchronouse actve high reset
  input  logic [9:0]                 hart_base_id_i,
  input  snitch_axi_pkg::req_t       axi_slv_req_i,
  output snitch_axi_pkg::resp_t      axi_slv_res_o,
  output snitch_axi_pkg::req_slv_t   axi_mst_req_o,
  input  snitch_axi_pkg::resp_slv_t  axi_mst_res_i
);

  snitch_sdma_cluster #(
    .BootAddr              ( BootAddr            ),
    .MTVEC                 ( MTVEC               ),
    .NrCores               ( NrCores             ),
    .BankFactor            ( BankFactor          ),
    .RVE                   ( RVE                 ),
    .RVFD                  ( RVFD                ),
    .InstDepth             ( InstDepth           ),
    .TCDMDepth             ( TCDMDepth           ),
    .Topology              ( Topology            ),
    .RegisterAmo           ( RegisterAmo         ),
    .RegisterOffload       ( RegisterOffload     ),
    .RegisterOffloadRsp    ( RegisterOffloadRsp  ),
    .RegisterTCDMReq       ( RegisterTCDMReq     ),
    .CoresPerHive          ( CoresPerHive        ),
    .ICacheSets            ( ICacheSets          ),
    .NumPar                ( NumPar              ),
    .SDMA                  ( 0                   )
  ) i_snitch_sdma_cluster_legacy (
    .clk_i           ( clk_i          ),
    .rst_i           ( rst_i          ),
    .hart_base_id_i  ( hart_base_id_i ),
    .axi_slv_req_i   ( axi_slv_req_i  ), // External Master (Snitch Slave Port)
    .axi_slv_res_o   ( axi_slv_res_o  ), // External Master (Snitch Slave Port)
    .axi_mst_req_o   ( axi_mst_req_o  ), // External Slave (Snitch Master Port)
    .axi_mst_res_i   ( axi_mst_res_i  ), // External Slave (Snitch Master Port)
    .ext_dma_req_o   ( ),
    .ext_dma_resp_i  ( '0             )
  );

endmodule : snitch_cluster
