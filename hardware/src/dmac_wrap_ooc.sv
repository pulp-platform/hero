// ooc wrapper
module dmac_wrap_ooc (
  input  logic          clk_i,
  input  logic          rst_ni,
  input  logic          test_mode_i,

  output logic [31:0]   data_master_aw_addr_o,
  output logic [2:0]    data_master_aw_prot_o,
  output logic [3:0]    data_master_aw_region_o,
  output logic [7:0]    data_master_aw_len_o,
  output logic [2:0]    data_master_aw_size_o,
  output logic [1:0]    data_master_aw_burst_o,
  output logic          data_master_aw_lock_o,
  output logic [5:0]    data_master_aw_atop_o,
  output logic [3:0]    data_master_aw_cache_o,
  output logic [3:0]    data_master_aw_qos_o,
  output logic [3:0]    data_master_aw_id_o,
  output logic [3:0]    data_master_aw_user_o,
  output logic          data_master_aw_valid_o,
  input  logic          data_master_aw_ready_i,

  output logic [31:0]   data_master_ar_addr_o,
  output logic [2:0]    data_master_ar_prot_o,
  output logic [3:0]    data_master_ar_region_o,
  output logic [7:0]    data_master_ar_len_o,
  output logic [2:0]    data_master_ar_size_o,
  output logic [1:0]    data_master_ar_burst_o,
  output logic          data_master_ar_lock_o,
  output logic [3:0]    data_master_ar_cache_o,
  output logic [3:0]    data_master_ar_qos_o,
  output logic [3:0]    data_master_ar_id_o,
  output logic [3:0]    data_master_ar_user_o,
  output logic          data_master_ar_valid_o,
  input  logic          data_master_ar_ready_i,

  output logic [63:0]   data_master_w_data_o,
  output logic [7:0]    data_master_w_strb_o,
  output logic [3:0]    data_master_w_user_o,
  output logic          data_master_w_last_o,
  output logic          data_master_w_valid_o,
  input  logic          data_master_w_ready_i,

  input  logic [63:0]   data_master_r_data_i,
  input  logic [1:0]    data_master_r_resp_i,
  input  logic          data_master_r_last_i,
  input  logic [3:0]    data_master_r_id_i,
  input  logic [3:0]    data_master_r_user_i,
  input  logic          data_master_r_valid_i,
  output logic          data_master_r_ready_o,

  input  logic [1:0]    data_master_b_resp_i,
  input  logic [3:0]    data_master_b_id_i,
  input  logic [3:0]    data_master_b_user_i,
  input  logic          data_master_b_valid_i,
  output logic          data_master_b_ready_o,

  input  logic          pe_ctrl_0_req,
  input  logic [31:0]   pe_ctrl_0_add,
  input  logic          pe_ctrl_0_wen,
  input  logic [31:0]   pe_ctrl_0_wdata,
  input  logic  [3:0]   pe_ctrl_0_be,
  output logic          pe_ctrl_0_gnt,
  output logic          pe_ctrl_0_r_opc,
  output logic [31:0]   pe_ctrl_0_r_rdata,
  output logic          pe_ctrl_0_r_valid,

  input  logic          pe_ctrl_1_req,
  input  logic [31:0]   pe_ctrl_1_add,
  input  logic          pe_ctrl_1_wen,
  input  logic [31:0]   pe_ctrl_1_wdata,
  input  logic  [3:0]   pe_ctrl_1_be,
  output logic          pe_ctrl_1_gnt,
  output logic          pe_ctrl_1_r_opc,
  output logic [31:0]   pe_ctrl_1_r_rdata,
  output logic          pe_ctrl_1_r_valid,

  input  logic          pe_ctrl_2_req,
  input  logic [31:0]   pe_ctrl_2_add,
  input  logic          pe_ctrl_2_wen,
  input  logic [31:0]   pe_ctrl_2_wdata,
  input  logic  [3:0]   pe_ctrl_2_be,
  output logic          pe_ctrl_2_gnt,
  output logic          pe_ctrl_2_r_opc,
  output logic [31:0]   pe_ctrl_2_r_rdata,
  output logic          pe_ctrl_2_r_valid,

  input  logic          pe_ctrl_3_req,
  input  logic [31:0]   pe_ctrl_3_add,
  input  logic          pe_ctrl_3_wen,
  input  logic [31:0]   pe_ctrl_3_wdata,
  input  logic  [3:0]   pe_ctrl_3_be,
  output logic          pe_ctrl_3_gnt,
  output logic          pe_ctrl_3_r_opc,
  output logic [31:0]   pe_ctrl_3_r_rdata,
  output logic          pe_ctrl_3_r_valid,

  input  logic          pe_ctrl_4_req,
  input  logic [31:0]   pe_ctrl_4_add,
  input  logic          pe_ctrl_4_wen,
  input  logic [31:0]   pe_ctrl_4_wdata,
  input  logic  [3:0]   pe_ctrl_4_be,
  output logic          pe_ctrl_4_gnt,
  output logic          pe_ctrl_4_r_opc,
  output logic [31:0]   pe_ctrl_4_r_rdata,
  output logic          pe_ctrl_4_r_valid,

  input  logic          pe_ctrl_5_req,
  input  logic [31:0]   pe_ctrl_5_add,
  input  logic          pe_ctrl_5_wen,
  input  logic [31:0]   pe_ctrl_5_wdata,
  input  logic  [3:0]   pe_ctrl_5_be,
  output logic          pe_ctrl_5_gnt,
  output logic          pe_ctrl_5_r_opc,
  output logic [31:0]   pe_ctrl_5_r_rdata,
  output logic          pe_ctrl_5_r_valid,

  input  logic          pe_ctrl_6_req,
  input  logic [31:0]   pe_ctrl_6_add,
  input  logic          pe_ctrl_6_wen,
  input  logic [31:0]   pe_ctrl_6_wdata,
  input  logic  [3:0]   pe_ctrl_6_be,
  output logic          pe_ctrl_6_gnt,
  output logic          pe_ctrl_6_r_opc,
  output logic [31:0]   pe_ctrl_6_r_rdata,
  output logic          pe_ctrl_6_r_valid,

  input  logic          pe_ctrl_7_req,
  input  logic [31:0]   pe_ctrl_7_add,
  input  logic          pe_ctrl_7_wen,
  input  logic [31:0]   pe_ctrl_7_wdata,
  input  logic  [3:0]   pe_ctrl_7_be,
  output logic          pe_ctrl_7_gnt,
  output logic          pe_ctrl_7_r_opc,
  output logic [31:0]   pe_ctrl_7_r_rdata,
  output logic          pe_ctrl_7_r_valid,

  output logic          tcdm_0_req,
  output logic [31:0]   tcdm_0_add,
  output logic          tcdm_0_wen,
  output logic [31:0]   tcdm_0_wdata,
  output logic  [3:0]   tcdm_0_be,
  input  logic          tcdm_0_gnt,
  input  logic          tcdm_0_r_opc,
  input  logic [31:0]   tcdm_0_r_rdata,
  input  logic          tcdm_0_r_valid,

  output logic          tcdm_1_req,
  output logic [31:0]   tcdm_1_add,
  output logic          tcdm_1_wen,
  output logic [31:0]   tcdm_1_wdata,
  output logic  [3:0]   tcdm_1_be,
  input  logic          tcdm_1_gnt,
  input  logic          tcdm_1_r_opc,
  input  logic [31:0]   tcdm_1_r_rdata,
  input  logic          tcdm_1_r_valid,

  output logic          tcdm_2_req,
  output logic [31:0]   tcdm_2_add,
  output logic          tcdm_2_wen,
  output logic [31:0]   tcdm_2_wdata,
  output logic  [3:0]   tcdm_2_be,
  input  logic          tcdm_2_gnt,
  input  logic          tcdm_2_r_opc,
  input  logic [31:0]   tcdm_2_r_rdata,
  input  logic          tcdm_2_r_valid,

  output logic          tcdm_3_req,
  output logic [31:0]   tcdm_3_add,
  output logic          tcdm_3_wen,
  output logic [31:0]   tcdm_3_wdata,
  output logic  [3:0]   tcdm_3_be,
  input  logic          tcdm_3_gnt,
  input  logic          tcdm_3_r_opc,
  input  logic [31:0]   tcdm_3_r_rdata,
  input  logic          tcdm_3_r_valid,

  input  logic          ctrl_req,
  input  logic [31:0]   ctrl_add,
  input  logic          ctrl_wen,
  input  logic [31:0]   ctrl_wdata,
  input  logic  [3:0]   ctrl_be,
  output logic          ctrl_gnt,
  input  logic  [8:0]   ctrl_id,
  output logic          ctrl_r_valid,
  output logic          ctrl_r_opc,
  output logic  [8:0]   ctrl_r_id,
  output logic [31:0]   ctrl_r_rdata,

  output logic [7:0]    term_event_o,
  output logic [7:0]    term_irq_o,
  output logic          term_event_pe_o,
  output logic          term_irq_pe_o,
  output logic          busy_o
);

  XBAR_TCDM_BUS pe_ctrl_slave[7:0]();
  XBAR_PERIPH_BUS ctrl_slave();
  XBAR_TCDM_BUS tcdm_master[3:0]();
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( 32  ),
    .AXI_DATA_WIDTH ( 64  ),
    .AXI_ID_WIDTH   (  4  ),
    .AXI_USER_WIDTH (  4  )
  ) ext_master();

  dmac_wrap #(
    .NB_CORES           ( 8      ),
    /*.NB_OUTSND_BURSTS   ( 8      ),
    .MCHAN_BURST_LENGTH ( 2048   ),*/
    .AXI_ADDR_WIDTH     ( 32     ),
    .AXI_DATA_WIDTH     ( 64     ),
    .AXI_USER_WIDTH     ( 4      ),
    .AXI_ID_WIDTH       ( 4      ),
    .PE_ID_WIDTH        ( 9      ),
    /*.TCDM_ADD_WIDTH     ( 16     ),*/
    .DATA_WIDTH         ( 32     ),
    .ADDR_WIDTH         ( 32     ),
    .NUM_STREAMS        ( 4      )
  ) i_dmac_wrap (
    .clk_i            ( clk_i             ),
    .rst_ni           ( rst_ni            ),
    .test_mode_i      ( test_mode_i       ),
    .pe_ctrl_slave    ( ctrl_slave        ),
    .ctrl_slave       ( pe_ctrl_slave     ),
    .tcdm_master      ( tcdm_master       ),
    .ext_master       ( ext_master        ),
    .term_event_o     ( term_event_o      ),
    .term_irq_o       ( term_irq_o        ),
    .term_event_pe_o  ( term_event_pe_o   ),
    .term_irq_pe_o    ( term_irq_pe_o     ),
    .busy_o           ( busy_o            )
  );

  assign data_master_aw_valid_o     = ext_master.aw_valid;
  assign data_master_aw_addr_o      = ext_master.aw_addr;
  assign data_master_aw_prot_o      = ext_master.aw_prot;
  assign data_master_aw_region_o    = ext_master.aw_region;
  assign data_master_aw_len_o       = ext_master.aw_len;
  assign data_master_aw_size_o      = ext_master.aw_size;
  assign data_master_aw_burst_o     = ext_master.aw_burst;
  assign data_master_aw_lock_o      = ext_master.aw_lock;
  assign data_master_aw_atop_o      = ext_master.aw_atop;
  assign data_master_aw_cache_o     = ext_master.aw_cache;
  assign data_master_aw_qos_o       = ext_master.aw_qos;
  assign data_master_aw_id_o        = ext_master.aw_id;
  assign data_master_aw_user_o      = ext_master.aw_user;
  assign ext_master.aw_ready        = data_master_aw_ready_i;

  assign data_master_ar_valid_o     = ext_master.ar_valid;
  assign data_master_ar_addr_o      = ext_master.ar_addr;
  assign data_master_ar_prot_o      = ext_master.ar_prot;
  assign data_master_ar_region_o    = ext_master.ar_region;
  assign data_master_ar_len_o       = ext_master.ar_len;
  assign data_master_ar_size_o      = ext_master.ar_size;
  assign data_master_ar_burst_o     = ext_master.ar_burst;
  assign data_master_ar_lock_o      = ext_master.ar_lock;
  assign data_master_ar_cache_o     = ext_master.ar_cache;
  assign data_master_ar_qos_o       = ext_master.ar_qos;
  assign data_master_ar_id_o        = ext_master.ar_id;
  assign data_master_ar_user_o      = ext_master.ar_user;
  assign ext_master.ar_ready        = data_master_ar_ready_i;

  assign data_master_w_valid_o      = ext_master.w_valid;
  assign data_master_w_data_o       = ext_master.w_data;
  assign data_master_w_strb_o       = ext_master.w_strb;
  assign data_master_w_user_o       = ext_master.w_user;
  assign data_master_w_last_o       = ext_master.w_last;
  assign ext_master.w_ready         = data_master_w_ready_i;

  assign ext_master.r_valid         = data_master_r_valid_i;
  assign ext_master.r_data          = data_master_r_data_i;
  assign ext_master.r_resp          = data_master_r_resp_i;
  assign ext_master.r_last          = data_master_r_last_i;
  assign ext_master.r_id            = data_master_r_id_i;
  assign ext_master.r_user          = data_master_r_user_i;
  assign data_master_r_ready_o      = ext_master.r_ready;

  assign ext_master.b_valid         = data_master_b_valid_i;
  assign ext_master.b_resp          = data_master_b_resp_i;
  assign ext_master.b_id            = data_master_b_id_i;
  assign ext_master.b_user          = data_master_b_user_i;
  assign data_master_b_ready_o      = ext_master.b_ready;

  assign pe_ctrl_slave[0].req   = pe_ctrl_0_req;
  assign pe_ctrl_slave[0].add   = pe_ctrl_0_add;
  assign pe_ctrl_slave[0].wen   = pe_ctrl_0_wen;
  assign pe_ctrl_slave[0].wdata = pe_ctrl_0_wdata;
  assign pe_ctrl_slave[0].be    = pe_ctrl_0_be;
  assign pe_ctrl_0_gnt          = pe_ctrl_slave[0].gnt;
  assign pe_ctrl_0_r_opc        = pe_ctrl_slave[0].r_opc;
  assign pe_ctrl_0_r_rdata      = pe_ctrl_slave[0].r_rdata;
  assign pe_ctrl_0_r_valid      = pe_ctrl_slave[0].r_valid;

  assign pe_ctrl_slave[1].req   = pe_ctrl_1_req;
  assign pe_ctrl_slave[1].add   = pe_ctrl_1_add;
  assign pe_ctrl_slave[1].wen   = pe_ctrl_1_wen;
  assign pe_ctrl_slave[1].wdata = pe_ctrl_1_wdata;
  assign pe_ctrl_slave[1].be    = pe_ctrl_1_be;
  assign pe_ctrl_1_gnt          = pe_ctrl_slave[1].gnt;
  assign pe_ctrl_1_r_opc        = pe_ctrl_slave[1].r_opc;
  assign pe_ctrl_1_r_rdata      = pe_ctrl_slave[1].r_rdata;
  assign pe_ctrl_1_r_valid      = pe_ctrl_slave[1].r_valid;

  assign pe_ctrl_slave[2].req   = pe_ctrl_2_req;
  assign pe_ctrl_slave[2].add   = pe_ctrl_2_add;
  assign pe_ctrl_slave[2].wen   = pe_ctrl_2_wen;
  assign pe_ctrl_slave[2].wdata = pe_ctrl_2_wdata;
  assign pe_ctrl_slave[2].be    = pe_ctrl_2_be;
  assign pe_ctrl_2_gnt          = pe_ctrl_slave[2].gnt;
  assign pe_ctrl_2_r_opc        = pe_ctrl_slave[2].r_opc;
  assign pe_ctrl_2_r_rdata      = pe_ctrl_slave[2].r_rdata;
  assign pe_ctrl_2_r_valid      = pe_ctrl_slave[2].r_valid;

  assign pe_ctrl_slave[3].req   = pe_ctrl_3_req;
  assign pe_ctrl_slave[3].add   = pe_ctrl_3_add;
  assign pe_ctrl_slave[3].wen   = pe_ctrl_3_wen;
  assign pe_ctrl_slave[3].wdata = pe_ctrl_3_wdata;
  assign pe_ctrl_slave[3].be    = pe_ctrl_3_be;
  assign pe_ctrl_3_gnt          = pe_ctrl_slave[3].gnt;
  assign pe_ctrl_3_r_opc        = pe_ctrl_slave[3].r_opc;
  assign pe_ctrl_3_r_rdata      = pe_ctrl_slave[3].r_rdata;
  assign pe_ctrl_3_r_valid      = pe_ctrl_slave[3].r_valid;

  assign pe_ctrl_slave[4].req   = pe_ctrl_4_req;
  assign pe_ctrl_slave[4].add   = pe_ctrl_4_add;
  assign pe_ctrl_slave[4].wen   = pe_ctrl_4_wen;
  assign pe_ctrl_slave[4].wdata = pe_ctrl_4_wdata;
  assign pe_ctrl_slave[4].be    = pe_ctrl_4_be;
  assign pe_ctrl_4_gnt          = pe_ctrl_slave[4].gnt;
  assign pe_ctrl_4_r_opc        = pe_ctrl_slave[4].r_opc;
  assign pe_ctrl_4_r_rdata      = pe_ctrl_slave[4].r_rdata;
  assign pe_ctrl_4_r_valid      = pe_ctrl_slave[4].r_valid;

  assign pe_ctrl_slave[5].req   = pe_ctrl_5_req;
  assign pe_ctrl_slave[5].add   = pe_ctrl_5_add;
  assign pe_ctrl_slave[5].wen   = pe_ctrl_5_wen;
  assign pe_ctrl_slave[5].wdata = pe_ctrl_5_wdata;
  assign pe_ctrl_slave[5].be    = pe_ctrl_5_be;
  assign pe_ctrl_5_gnt          = pe_ctrl_slave[5].gnt;
  assign pe_ctrl_5_r_opc        = pe_ctrl_slave[5].r_opc;
  assign pe_ctrl_5_r_rdata      = pe_ctrl_slave[5].r_rdata;
  assign pe_ctrl_5_r_valid      = pe_ctrl_slave[5].r_valid;

  assign pe_ctrl_slave[6].req   = pe_ctrl_6_req;
  assign pe_ctrl_slave[6].add   = pe_ctrl_6_add;
  assign pe_ctrl_slave[6].wen   = pe_ctrl_6_wen;
  assign pe_ctrl_slave[6].wdata = pe_ctrl_6_wdata;
  assign pe_ctrl_slave[6].be    = pe_ctrl_6_be;
  assign pe_ctrl_6_gnt          = pe_ctrl_slave[6].gnt;
  assign pe_ctrl_6_r_opc        = pe_ctrl_slave[6].r_opc;
  assign pe_ctrl_6_r_rdata      = pe_ctrl_slave[6].r_rdata;
  assign pe_ctrl_6_r_valid      = pe_ctrl_slave[6].r_valid;

  assign pe_ctrl_slave[7].req   = pe_ctrl_7_req;
  assign pe_ctrl_slave[7].add   = pe_ctrl_7_add;
  assign pe_ctrl_slave[7].wen   = pe_ctrl_7_wen;
  assign pe_ctrl_slave[7].wdata = pe_ctrl_7_wdata;
  assign pe_ctrl_slave[7].be    = pe_ctrl_7_be;
  assign pe_ctrl_7_gnt          = pe_ctrl_slave[7].gnt;
  assign pe_ctrl_7_r_opc        = pe_ctrl_slave[7].r_opc;
  assign pe_ctrl_7_r_rdata      = pe_ctrl_slave[7].r_rdata;
  assign pe_ctrl_7_r_valid      = pe_ctrl_slave[7].r_valid;

  assign tcdm_0_req             = tcdm_master[0].req;
  assign tcdm_0_add             = tcdm_master[0].add;
  assign tcdm_0_wen             = tcdm_master[0].wen;
  assign tcdm_0_wdata           = tcdm_master[0].wdata;
  assign tcdm_0_be              = tcdm_master[0].be;
  assign tcdm_master[0].gnt     = tcdm_0_gnt;
  assign tcdm_master[0].r_opc   = tcdm_0_r_opc;
  assign tcdm_master[0].r_rdata = tcdm_0_r_rdata;
  assign tcdm_master[0].r_valid = tcdm_0_r_valid;

  assign tcdm_1_req             = tcdm_master[1].req;
  assign tcdm_1_add             = tcdm_master[1].add;
  assign tcdm_1_wen             = tcdm_master[1].wen;
  assign tcdm_1_wdata           = tcdm_master[1].wdata;
  assign tcdm_1_be              = tcdm_master[1].be;
  assign tcdm_master[1].gnt     = tcdm_1_gnt;
  assign tcdm_master[1].r_opc   = tcdm_1_r_opc;
  assign tcdm_master[1].r_rdata = tcdm_1_r_rdata;
  assign tcdm_master[1].r_valid = tcdm_1_r_valid;

  assign tcdm_2_req             = tcdm_master[2].req;
  assign tcdm_2_add             = tcdm_master[2].add;
  assign tcdm_2_wen             = tcdm_master[2].wen;
  assign tcdm_2_wdata           = tcdm_master[2].wdata;
  assign tcdm_2_be              = tcdm_master[2].be;
  assign tcdm_master[2].gnt     = tcdm_2_gnt;
  assign tcdm_master[2].r_opc   = tcdm_2_r_opc;
  assign tcdm_master[2].r_rdata = tcdm_2_r_rdata;
  assign tcdm_master[2].r_valid = tcdm_2_r_valid;

  assign tcdm_3_req             = tcdm_master[3].req;
  assign tcdm_3_add             = tcdm_master[3].add;
  assign tcdm_3_wen             = tcdm_master[3].wen;
  assign tcdm_3_wdata           = tcdm_master[3].wdata;
  assign tcdm_3_be              = tcdm_master[3].be;
  assign tcdm_master[3].gnt     = tcdm_3_gnt;
  assign tcdm_master[3].r_opc   = tcdm_3_r_opc;
  assign tcdm_master[3].r_rdata = tcdm_3_r_rdata;
  assign tcdm_master[3].r_valid = tcdm_3_r_valid;

  assign ctrl_slave.req       = ctrl_req;
  assign ctrl_slave.add       = ctrl_add;
  assign ctrl_slave.wen       = ctrl_wen;
  assign ctrl_slave.wdata     = ctrl_wdata;
  assign ctrl_slave.be        = ctrl_be;
  assign ctrl_gnt             = ctrl_slave.gnt;
  assign ctrl_slave.id        = ctrl_id;
  assign ctrl_r_valid         = ctrl_slave.r_valid;
  assign ctrl_r_opc           = ctrl_slave.r_opc;
  assign ctrl_r_id            = ctrl_slave.r_id;
  assign ctrl_r_rdata         = ctrl_slave.r_rdata;

endmodule : dmac_wrap_ooc
