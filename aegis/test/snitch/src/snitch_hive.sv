/// Batches up couple of Snitch cores which share an instruction frontend
/// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
module snitch_hive #(
  parameter int unsigned CoreCount          = 4,       // Number of cores which share an instruction frontend
  parameter int unsigned MaxNumCompCores    = 65536,
  parameter int unsigned ICacheSizeByte     = 1024 * CoreCount, // Total Size of instruction cache in bytes
  parameter int unsigned ICacheSets         = CoreCount,
  parameter logic [31:0] BootAddr           = 32'h0,
  parameter logic [31:0] MTVEC              = BootAddr,
  parameter bit          RVE                = 0,       // Reduced-register extension
  parameter bit          RVFD               = 1,       // Enable F and D Extension
  parameter bit          SDMA               = 0,       // Include the fabric controller with DMA (frankensnitch)
  parameter bit          RegisterOffload    = 1,  // Insert Pipeline registers into off-loading path (request)
  parameter bit          RegisterOffloadRsp = 0,  // Insert Pipeline registers into off-loading path (response)
  parameter bit          RegisterTCDMReq    = 1,   // Insert Pipeline registers into data memory request path
  parameter type         axi_dma_req_t      = logic,
  parameter type         axi_dma_res_t      = logic
) (
  input  logic                       clk_i,
  input  logic                       rst_i,
  input  logic [31:0]                hart_base_id_i,
  // TCDM Ports
  output snitch_pkg::addr_t [CoreCount-1:0][1:0] data_qaddr_o,
  output logic [CoreCount-1:0][1:0]       data_qwrite_o,
  output logic [CoreCount-1:0][1:0][3:0]  data_qamo_o,
  output logic [CoreCount-1:0][1:0][63:0] data_qdata_o,
  output logic [CoreCount-1:0][1:0][1:0]  data_qsize_o,
  output logic [CoreCount-1:0][1:0][7:0]  data_qstrb_o,
  output logic [CoreCount-1:0][1:0]       data_qvalid_o,
  input  logic [CoreCount-1:0][1:0]       data_qready_i,
  input  logic [CoreCount-1:0][1:0][63:0] data_pdata_i,
  input  logic [CoreCount-1:0][1:0]       data_perror_i,
  input  logic [CoreCount-1:0][1:0]       data_pvalid_i,
  output logic [CoreCount-1:0][1:0]       data_pready_o,
  input  logic [CoreCount-1:0]            wake_up_sync_i,

  // I-Cache refill interface
  output logic [31:0]                refill_qaddr_o,
  output logic [7:0]                 refill_qlen_o,
  output logic                       refill_qvalid_o,
  input  logic                       refill_qready_i,
  input  logic [63:0]                refill_pdata_i,
  input  logic                       refill_perror_i,
  input  logic                       refill_pvalid_i,
  input  logic                       refill_plast_i,
  output logic                       refill_pready_o,

  // DMA ports
  output snitch_axi_pkg::req_dma_t   axi_dma_req_o,
  input  snitch_axi_pkg::resp_dma_t  axi_dma_res_i,
  output logic                       axi_dma_busy_o,
  output axi_dma_pkg::dma_perf_t     axi_dma_perf_o,

  output snitch_pkg::core_events_t [CoreCount-1:0] core_events_o
);
  // Extend the ID to route back results to the appropriate core.
  localparam int unsigned IdWidth = 5;
  localparam int unsigned LogCoreCount = CoreCount > 1 ? $clog2(CoreCount) : 1;
  localparam int unsigned ExtendedIdWidth = IdWidth + LogCoreCount;

  logic [CoreCount-1:0][31:0] inst_addr;
  logic [CoreCount-1:0]       inst_cacheable;
  logic [CoreCount-1:0][31:0] inst_data;
  logic [CoreCount-1:0]       inst_valid;
  logic [CoreCount-1:0]       inst_ready;
  logic [CoreCount-1:0]       inst_error;

  logic [CoreCount-1:0]       flush_valid;
  logic [CoreCount-1:0]       flush_ready;
  logic flush_ready_ic;

  typedef struct packed {
    logic [31:0]                addr;
    logic [ExtendedIdWidth-1:0] id;
    logic [31:0]                data_op;
    logic [63:0]                data_arga;
    logic [63:0]                data_argb;
    logic [63:0]                data_argc;
  } acc_req_t;

  typedef struct packed {
    logic [ExtendedIdWidth-1:0] id;
    logic                       error;
    logic [63:0]                data;
  } acc_resp_t;

  snitch_pkg::acc_req_t  [CoreCount-1:0] acc_req;
  acc_req_t              [CoreCount-1:0] acc_req_ext; // extended version
  logic                  [CoreCount-1:0] acc_qvalid;
  logic                  [CoreCount-1:0] acc_qready;
  snitch_pkg::acc_resp_t [CoreCount-1:0] acc_resp;
  logic                  [CoreCount-1:0] acc_pvalid;
  logic                  [CoreCount-1:0] acc_pready;

  acc_req_t              acc_req_sfu, acc_req_sfu_q; // to shared functional unit
  logic                  acc_req_sfu_valid, acc_req_sfu_valid_q;
  logic                  acc_req_sfu_ready, acc_req_sfu_ready_q;

  acc_resp_t             acc_resp_sfu; // to shared functional unit
  logic                  acc_resp_sfu_valid;
  logic                  acc_resp_sfu_ready;

  localparam int LineWidth = ((CoreCount-SDMA) * 32 < 64) ? 64 : (CoreCount-SDMA) * 32;

  snitch_icache #(
    .NR_FETCH_PORTS    ( CoreCount                                                 ),
    /// Cache Line Width
    .L0_LINE_COUNT     ( 4                                                         ),
    .LINE_WIDTH        ( LineWidth                                                 ),
    .LINE_COUNT        ( ICacheSizeByte / ((CoreCount-SDMA) * (CoreCount-SDMA) * 4) ),
    .SET_COUNT         ( ICacheSets                                                ),
    .FETCH_AW          ( 32                                                        ),
    .FETCH_DW          ( 32                                                        ),
    .FILL_AW           ( 32                                                        ),
    .FILL_DW           ( 64                                                        ),
    .EARLY_ENABLED     ( 1                                                         ),
    /// Make the early cache latch-based. This reduces latency at the cost of
    /// increased combinatorial path lengths and the hassle of having latches in
    /// the design.
    .EARLY_LATCH       ( 0                                                         ),
    /// Make the early cache serve responses combinatorially if possible. Set
    /// this to 0 to cut combinatorial paths into the fetch interface.
    .EARLY_FALLTHROUGH ( 0                                                         )
  ) i_snitch_icache (
    .clk_i                          ,
    .rst_ni          ( ~rst_i      ),
    .flush_valid_i   ( |flush_valid   ),
    .flush_ready_o   ( flush_ready_ic ),

    .inst_addr_i      ( inst_addr      ),
    .inst_cacheable_i ( inst_cacheable ),
    .inst_data_o      ( inst_data      ),
    .inst_valid_i     ( inst_valid     ),
    .inst_ready_o     ( inst_ready     ),
    .inst_error_o     ( inst_error     ),

    .refill_qaddr_o,
    .refill_qlen_o,
    .refill_qvalid_o,
    .refill_qready_i,

    .refill_pdata_i,
    .refill_perror_i,
    .refill_pvalid_i,
    .refill_plast_i,
    .refill_pready_o
  );

  assign flush_ready = {{CoreCount}{flush_ready_ic}};

  for (genvar i = 0; i < CoreCount; i++) begin : gen_core
      // If enable the DMA core is always in the last core of a cluster
      localparam bit IsSDMACore = SDMA && (i == (CoreCount - 1));
      snitch_axi_pkg::req_dma_t   axi_dma_req;
      snitch_axi_pkg::resp_dma_t  axi_dma_res;
      logic                       axi_dma_busy;
      axi_dma_pkg::dma_perf_t     axi_dma_perf;

      snitch_cc #(
        .BootAddr           ( BootAddr            ),
        .MTVEC              ( MTVEC               ),
        .RVE                ( RVE                 ),
        .RVFD               ( RVFD && !IsSDMACore ),
        .SDMA               ( IsSDMACore          ),
        .RegisterOffload    ( RegisterOffload     ),
        .RegisterOffloadRsp ( RegisterOffloadRsp  ),
        .RegisterTCDMReq    ( RegisterTCDMReq     )
      ) i_snitch_cc (
        .clk_i                                  ,
        .rst_i                                  ,
        .hart_id_i        ( hart_base_id_i + i ),
        .flush_i_valid_o  ( flush_valid    [i] ),
        .flush_i_ready_i  ( flush_ready    [i] ),
        .inst_addr_o      ( inst_addr      [i] ),
        .inst_cacheable_o ( inst_cacheable [i] ),
        .inst_data_i      ( inst_data      [i] ),
        .inst_valid_o     ( inst_valid     [i] ),
        .inst_ready_i     ( inst_ready     [i] ),
        .data_qaddr_o     ( data_qaddr_o   [i] ),
        .data_qwrite_o    ( data_qwrite_o  [i] ),
        .data_qamo_o      ( data_qamo_o    [i] ),
        .data_qdata_o     ( data_qdata_o   [i] ),
        .data_qsize_o     ( data_qsize_o   [i] ),
        .data_qstrb_o     ( data_qstrb_o   [i] ),
        .data_qvalid_o    ( data_qvalid_o  [i] ),
        .data_qready_i    ( data_qready_i  [i] ),
        .data_pdata_i     ( data_pdata_i   [i] ),
        .data_perror_i    ( data_perror_i  [i] ),
        .data_pvalid_i    ( data_pvalid_i  [i] ),
        .data_pready_o    ( data_pready_o  [i] ),
        .wake_up_sync_i   ( wake_up_sync_i [i] ),
        .acc_req_o        ( acc_req        [i] ),
        .acc_qvalid_o     ( acc_qvalid     [i] ),
        .acc_qready_i     ( acc_qready     [i] ),
        .acc_resp_i       ( acc_resp       [i] ),
        .acc_pvalid_i     ( acc_pvalid     [i] ),
        .acc_pready_o     ( acc_pready     [i] ),
        .core_events_o    ( core_events_o  [i] ),
        .axi_dma_req_o    ( axi_dma_req        ),
        .axi_dma_res_i    ( axi_dma_res        ),
        .axi_dma_busy_o   ( axi_dma_busy       ),
        .axi_dma_perf_o   ( axi_dma_perf       )
      );

    if (IsSDMACore) begin : gen_dma_connection
      assign axi_dma_req_o = axi_dma_req;
      assign axi_dma_res = axi_dma_res_i;
      assign axi_dma_busy_o = axi_dma_busy;
      assign axi_dma_perf_o = axi_dma_perf;
    end else begin
      assign axi_dma_res = '0;
    end

    assign acc_req_ext[i].id = {i[LogCoreCount-1:0], acc_req[i].id};
    assign acc_req_ext[i].addr = acc_req[i].addr;
    assign acc_req_ext[i].data_op = acc_req[i].data_op;
    assign acc_req_ext[i].data_arga = acc_req[i].data_arga;
    assign acc_req_ext[i].data_argb = acc_req[i].data_argb;
    assign acc_req_ext[i].data_argc = acc_req[i].data_argc;
  end

  // ----------------------------------
  // Shared Accelerator Interconnect
  // ----------------------------------
  if (CoreCount > 1) begin : gen_shared_interconnect
    stream_arbiter #(
      .DATA_T  ( acc_req_t ),
      .N_INP   ( CoreCount ),
      .ARBITER ( "rr" )
    ) i_stream_arbiter (
      .clk_i       ( clk_i             ),
      .rst_ni      ( ~rst_i            ),
      .inp_data_i  ( acc_req_ext       ),
      .inp_valid_i ( acc_qvalid        ),
      .inp_ready_o ( acc_qready        ),
      .oup_data_o  ( acc_req_sfu       ),
      .oup_valid_o ( acc_req_sfu_valid ),
      .oup_ready_i ( acc_req_sfu_ready )
    );

  end else begin
    assign acc_req_sfu = acc_req_ext;
    assign acc_req_sfu_valid = acc_qvalid;
    assign acc_qready = acc_req_sfu_ready;
  end

  logic [LogCoreCount-1:0] resp_sel;
  assign resp_sel = acc_resp_sfu.id[ExtendedIdWidth-1:IdWidth];

  stream_demux #(
    .N_OUP ( CoreCount )
  ) i_stream_demux (
    .inp_valid_i ( acc_resp_sfu_valid ),
    .inp_ready_o ( acc_resp_sfu_ready ),
    .oup_sel_i   ( resp_sel           ),
    .oup_valid_o ( acc_pvalid         ),
    .oup_ready_i ( acc_pready         )
  );

  for (genvar i = 0; i < CoreCount; i++) begin : gen_id_extension
    // reduce IP width again
    assign acc_resp[i].id    = acc_resp_sfu.id[IdWidth-1:0];
    assign acc_resp[i].error = acc_resp_sfu.error;
    assign acc_resp[i].data  = acc_resp_sfu.data;
  end

  spill_register  #(
    .T      ( acc_req_t  ),
    .Bypass ( 1'b1       )
  ) i_spill_register_muldiv (
    .clk_i   ,
    .rst_ni  ( ~rst_i              ),
    .valid_i ( acc_req_sfu_valid   ),
    .ready_o ( acc_req_sfu_ready   ),
    .data_i  ( acc_req_sfu         ),
    .valid_o ( acc_req_sfu_valid_q ),
    .ready_i ( acc_req_sfu_ready_q ),
    .data_o  ( acc_req_sfu_q       )
  );

  snitch_shared_muldiv #(
    .IdWidth ( ExtendedIdWidth )
  ) i_snitch_shared_muldiv (
    .clk_i            ( clk_i                   ),
    .rst_i            ( rst_i                   ),
    .acc_qaddr_i      ( acc_req_sfu_q.addr      ),
    .acc_qid_i        ( acc_req_sfu_q.id        ),
    .acc_qdata_op_i   ( acc_req_sfu_q.data_op   ),
    .acc_qdata_arga_i ( acc_req_sfu_q.data_arga ),
    .acc_qdata_argb_i ( acc_req_sfu_q.data_argb ),
    .acc_qdata_argc_i ( acc_req_sfu_q.data_argc ),
    .acc_qvalid_i     ( acc_req_sfu_valid_q     ),
    .acc_qready_o     ( acc_req_sfu_ready_q     ),
    .acc_pdata_o      ( acc_resp_sfu.data       ),
    .acc_pid_o        ( acc_resp_sfu.id         ),
    .acc_perror_o     ( acc_resp_sfu.error      ),
    .acc_pvalid_o     ( acc_resp_sfu_valid      ),
    .acc_pready_i     ( acc_resp_sfu_ready      )
  );

  // pragma translate_off
  `ifndef VERILATOR
  // Check invariants.
  initial begin
      assert(BootAddr[1:0] == 2'b00);
      if (SDMA == 0) assert(2**LogCoreCount     == CoreCount     || CoreCount == 1) else $error("Core count must be a power of two");
      if (SDMA == 1) assert(2**(LogCoreCount-1) == (CoreCount-1) || CoreCount == 1) else $error("Core count must be a power of two + 1");
      assert(2**$clog2(ICacheSizeByte) == ICacheSizeByte);
  end
  `endif
  // pragma translate_on
endmodule
