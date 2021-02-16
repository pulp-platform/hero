`include "axi/typedef.svh"

module pulp_ooc #(
  parameter int unsigned  N_CLUSTERS = 4,
  parameter int unsigned  AXI_DW = 256,         // [bit]
  parameter int unsigned  L2_N_AXI_PORTS = 1,
  parameter type data_t = logic [AXI_DW-1:0],
  parameter type id_t = logic [pulp_pkg::axi_iw_sb_oup(N_CLUSTERS)-1:0],
  parameter type strb_t = logic [AXI_DW/8-1:0]
) (
  // Clocks and Resets
  input  logic              clk_i,
  input  logic              rst_ni,

  output id_t               mst_aw_id_o,
  output pulp_pkg::addr_t   mst_aw_addr_o,
  output axi_pkg::len_t     mst_aw_len_o,
  output axi_pkg::size_t    mst_aw_size_o,
  output axi_pkg::burst_t   mst_aw_burst_o,
  output logic              mst_aw_lock_o,
  output axi_pkg::cache_t   mst_aw_cache_o,
  output axi_pkg::prot_t    mst_aw_prot_o,
  output axi_pkg::qos_t     mst_aw_qos_o,
  output axi_pkg::region_t  mst_aw_region_o,
  output axi_pkg::atop_t    mst_aw_atop_o,
  output pulp_pkg::user_t   mst_aw_user_o,
  output logic              mst_aw_valid_o,
  input  logic              mst_aw_ready_i,
  output data_t             mst_w_data_o,
  output strb_t             mst_w_strb_o,
  output logic              mst_w_last_o,
  output pulp_pkg::user_t   mst_w_user_o,
  output logic              mst_w_valid_o,
  input  logic              mst_w_ready_i,
  input  id_t               mst_b_id_i,
  input  axi_pkg::resp_t    mst_b_resp_i,
  input  pulp_pkg::user_t   mst_b_user_i,
  input  logic              mst_b_valid_i,
  output logic              mst_b_ready_o,
  output id_t               mst_ar_id_o,
  output pulp_pkg::addr_t   mst_ar_addr_o,
  output axi_pkg::len_t     mst_ar_len_o,
  output axi_pkg::size_t    mst_ar_size_o,
  output axi_pkg::burst_t   mst_ar_burst_o,
  output logic              mst_ar_lock_o,
  output axi_pkg::cache_t   mst_ar_cache_o,
  output axi_pkg::prot_t    mst_ar_prot_o,
  output axi_pkg::qos_t     mst_ar_qos_o,
  output axi_pkg::region_t  mst_ar_region_o,
  output pulp_pkg::user_t   mst_ar_user_o,
  output logic              mst_ar_valid_o,
  input  logic              mst_ar_ready_i,
  input  id_t               mst_r_id_i,
  input  data_t             mst_r_data_i,
  input  axi_pkg::resp_t    mst_r_resp_i,
  input  logic              mst_r_last_i,
  input  pulp_pkg::user_t   mst_r_user_i,
  input  logic              mst_r_valid_i,
  output logic              mst_r_ready_o,

  input  id_t               slv_aw_id_i,
  input  pulp_pkg::addr_t   slv_aw_addr_i,
  input  axi_pkg::len_t     slv_aw_len_i,
  input  axi_pkg::size_t    slv_aw_size_i,
  input  axi_pkg::burst_t   slv_aw_burst_i,
  input  logic              slv_aw_lock_i,
  input  axi_pkg::cache_t   slv_aw_cache_i,
  input  axi_pkg::prot_t    slv_aw_prot_i,
  input  axi_pkg::qos_t     slv_aw_qos_i,
  input  axi_pkg::region_t  slv_aw_region_i,
  input  axi_pkg::atop_t    slv_aw_atop_i,
  input  pulp_pkg::user_t   slv_aw_user_i,
  input  logic              slv_aw_valid_i,
  output logic              slv_aw_ready_o,
  input  data_t             slv_w_data_i,
  input  strb_t             slv_w_strb_i,
  input  logic              slv_w_last_i,
  input  pulp_pkg::user_t   slv_w_user_i,
  input  logic              slv_w_valid_i,
  output logic              slv_w_ready_o,
  output id_t               slv_b_id_o,
  output axi_pkg::resp_t    slv_b_resp_o,
  output pulp_pkg::user_t   slv_b_user_o,
  output logic              slv_b_valid_o,
  input  logic              slv_b_ready_i,
  input  id_t               slv_ar_id_i,
  input  pulp_pkg::addr_t   slv_ar_addr_i,
  input  axi_pkg::len_t     slv_ar_len_i,
  input  axi_pkg::size_t    slv_ar_size_i,
  input  axi_pkg::burst_t   slv_ar_burst_i,
  input  logic              slv_ar_lock_i,
  input  axi_pkg::cache_t   slv_ar_cache_i,
  input  axi_pkg::prot_t    slv_ar_prot_i,
  input  axi_pkg::qos_t     slv_ar_qos_i,
  input  axi_pkg::region_t  slv_ar_region_i,
  input  pulp_pkg::user_t   slv_ar_user_i,
  input  logic              slv_ar_valid_i,
  output logic              slv_ar_ready_o,
  output id_t               slv_r_id_o,
  output data_t             slv_r_data_o,
  output axi_pkg::resp_t    slv_r_resp_o,
  output logic              slv_r_last_o,
  output pulp_pkg::user_t   slv_r_user_o,
  output logic              slv_r_valid_o,
  input  logic              slv_r_ready_i,

  input  pulp_pkg::lite_addr_t  rab_conf_aw_addr_i,
  input  axi_pkg::prot_t        rab_conf_aw_prot_i,
  input  logic                  rab_conf_aw_valid_i,
  output logic                  rab_conf_aw_ready_o,
  input  pulp_pkg::lite_data_t  rab_conf_w_data_i,
  input  pulp_pkg::lite_strb_t  rab_conf_w_strb_i,
  input  logic                  rab_conf_w_valid_i,
  output logic                  rab_conf_w_ready_o,
  output axi_pkg::resp_t        rab_conf_b_resp_o,
  output logic                  rab_conf_b_valid_o,
  input  logic                  rab_conf_b_ready_i,
  input  pulp_pkg::lite_addr_t  rab_conf_ar_addr_i,
  input  axi_pkg::prot_t        rab_conf_ar_prot_i,
  input  logic                  rab_conf_ar_valid_i,
  output logic                  rab_conf_ar_ready_o,
  output pulp_pkg::lite_data_t  rab_conf_r_data_o,
  output axi_pkg::resp_t        rab_conf_r_resp_o,
  output logic                  rab_conf_r_valid_o,
  input  logic                  rab_conf_r_ready_i,

  // Cluster Control
  input  logic [N_CLUSTERS-1:0] cl_fetch_en_i,
  output logic [N_CLUSTERS-1:0] cl_eoc_o,
  output logic [N_CLUSTERS-1:0] cl_busy_o,

  // RAB IRQs
  output logic  rab_from_pulp_miss_irq_o,
  output logic  rab_from_pulp_multi_irq_o,
  output logic  rab_from_pulp_prot_irq_o,
  output logic  rab_from_host_miss_irq_o,
  output logic  rab_from_host_multi_irq_o,
  output logic  rab_from_host_prot_irq_o,
  output logic  rab_miss_fifo_full_irq_o,
  // Mailbox IRQ
  output logic  mbox_irq_o
);

  `AXI_TYPEDEF_AW_CHAN_T(aw_t, pulp_pkg::addr_t, id_t, pulp_pkg::user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, pulp_pkg::user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_t, id_t, pulp_pkg::user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_t, pulp_pkg::addr_t, id_t, pulp_pkg::user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_t, data_t, id_t, pulp_pkg::user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_t, w_t, ar_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_t, r_t)

  `AXI_LITE_TYPEDEF_AW_CHAN_T(lite_aw_t, pulp_pkg::lite_addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(lite_w_t, pulp_pkg::lite_data_t, pulp_pkg::lite_strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(lite_b_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(lite_ar_t, pulp_pkg::lite_addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(lite_r_t, pulp_pkg::lite_data_t)
  `AXI_LITE_TYPEDEF_REQ_T(lite_req_t, lite_aw_t, lite_w_t, lite_ar_t)
  `AXI_LITE_TYPEDEF_RESP_T(lite_resp_t, lite_b_t, lite_r_t)

  req_t       to_pulp_req,
              from_pulp_req;
  resp_t      to_pulp_resp,
              from_pulp_resp;
  lite_req_t  rab_conf_req;
  lite_resp_t rab_conf_resp;

  assign mst_aw_id_o              = from_pulp_req.aw.id;
  assign mst_aw_addr_o            = from_pulp_req.aw.addr;
  assign mst_aw_len_o             = from_pulp_req.aw.len;
  assign mst_aw_size_o            = from_pulp_req.aw.size;
  assign mst_aw_burst_o           = from_pulp_req.aw.burst;
  assign mst_aw_lock_o            = from_pulp_req.aw.lock;
  assign mst_aw_cache_o           = from_pulp_req.aw.cache;
  assign mst_aw_prot_o            = from_pulp_req.aw.prot;
  assign mst_aw_qos_o             = from_pulp_req.aw.qos;
  assign mst_aw_region_o          = from_pulp_req.aw.region;
  assign mst_aw_atop_o            = from_pulp_req.aw.atop;
  assign mst_aw_user_o            = from_pulp_req.aw.user;
  assign mst_aw_valid_o           = from_pulp_req.aw_valid;
  assign from_pulp_resp.aw_ready  = mst_aw_ready_i;
  assign mst_w_data_o             = from_pulp_req.w.data;
  assign mst_w_strb_o             = from_pulp_req.w.strb;
  assign mst_w_last_o             = from_pulp_req.w.last;
  assign mst_w_user_o             = from_pulp_req.w.user;
  assign mst_w_valid_o            = from_pulp_req.w_valid;
  assign from_pulp_resp.w_ready   = mst_w_ready_i;
  assign from_pulp_resp.b.id      = mst_b_id_i;
  assign from_pulp_resp.b.resp    = mst_b_resp_i;
  assign from_pulp_resp.b.user    = mst_b_user_i;
  assign from_pulp_resp.b_valid   = mst_b_valid_i;
  assign mst_b_ready_o            = from_pulp_req.b_ready;
  assign mst_ar_id_o              = from_pulp_req.ar.id;
  assign mst_ar_addr_o            = from_pulp_req.ar.addr;
  assign mst_ar_len_o             = from_pulp_req.ar.len;
  assign mst_ar_size_o            = from_pulp_req.ar.size;
  assign mst_ar_burst_o           = from_pulp_req.ar.burst;
  assign mst_ar_lock_o            = from_pulp_req.ar.lock;
  assign mst_ar_cache_o           = from_pulp_req.ar.cache;
  assign mst_ar_prot_o            = from_pulp_req.ar.prot;
  assign mst_ar_qos_o             = from_pulp_req.ar.qos;
  assign mst_ar_region_o          = from_pulp_req.ar.region;
  assign mst_ar_user_o            = from_pulp_req.ar.user;
  assign mst_ar_valid_o           = from_pulp_req.ar_valid;
  assign from_pulp_resp.ar_ready  = mst_ar_ready_i;
  assign from_pulp_resp.r.id      = mst_r_id_i;
  assign from_pulp_resp.r.data    = mst_r_data_i;
  assign from_pulp_resp.r.resp    = mst_r_resp_i;
  assign from_pulp_resp.r.last    = mst_r_last_i;
  assign from_pulp_resp.r.user    = mst_r_user_i;
  assign from_pulp_resp.r_valid   = mst_r_valid_i;
  assign mst_r_ready_o            = from_pulp_req.r_ready;

  assign to_pulp_req.aw.id      = slv_aw_id_i;
  assign to_pulp_req.aw.addr    = slv_aw_addr_i;
  assign to_pulp_req.aw.len     = slv_aw_len_i;
  assign to_pulp_req.aw.size    = slv_aw_size_i;
  assign to_pulp_req.aw.burst   = slv_aw_burst_i;
  assign to_pulp_req.aw.lock    = slv_aw_lock_i;
  assign to_pulp_req.aw.cache   = slv_aw_cache_i;
  assign to_pulp_req.aw.prot    = slv_aw_prot_i;
  assign to_pulp_req.aw.qos     = slv_aw_qos_i;
  assign to_pulp_req.aw.region  = slv_aw_region_i;
  assign to_pulp_req.aw.atop    = slv_aw_atop_i;
  assign to_pulp_req.aw.user    = slv_aw_user_i;
  assign to_pulp_req.aw_valid   = slv_aw_valid_i;
  assign slv_aw_ready_o         = to_pulp_resp.aw_ready;
  assign to_pulp_req.w.data     = slv_w_data_i;
  assign to_pulp_req.w.strb     = slv_w_strb_i;
  assign to_pulp_req.w.last     = slv_w_last_i;
  assign to_pulp_req.w.user     = slv_w_user_i;
  assign to_pulp_req.w_valid    = slv_w_valid_i;
  assign slv_w_ready_o          = to_pulp_resp.w_ready;
  assign slv_b_id_o             = to_pulp_resp.b.id;
  assign slv_b_resp_o           = to_pulp_resp.b.resp;
  assign slv_b_user_o           = to_pulp_resp.b.user;
  assign slv_b_valid_o          = to_pulp_resp.b_valid;
  assign to_pulp_req.b_ready    = slv_b_ready_i;
  assign to_pulp_req.ar.id      = slv_ar_id_i;
  assign to_pulp_req.ar.addr    = slv_ar_addr_i;
  assign to_pulp_req.ar.len     = slv_ar_len_i;
  assign to_pulp_req.ar.size    = slv_ar_size_i;
  assign to_pulp_req.ar.burst   = slv_ar_burst_i;
  assign to_pulp_req.ar.lock    = slv_ar_lock_i;
  assign to_pulp_req.ar.cache   = slv_ar_cache_i;
  assign to_pulp_req.ar.prot    = slv_ar_prot_i;
  assign to_pulp_req.ar.qos     = slv_ar_qos_i;
  assign to_pulp_req.ar.region  = slv_ar_region_i;
  assign to_pulp_req.ar.user    = slv_ar_user_i;
  assign to_pulp_req.ar_valid   = slv_ar_valid_i;
  assign slv_ar_ready_o         = to_pulp_resp.ar_ready;
  assign slv_r_id_o             = to_pulp_resp.r.id;
  assign slv_r_data_o           = to_pulp_resp.r.data;
  assign slv_r_last_o           = to_pulp_resp.r.last;
  assign slv_r_resp_o           = to_pulp_resp.r.resp;
  assign slv_r_user_o           = to_pulp_resp.r.user;
  assign slv_r_valid_o          = to_pulp_resp.r_valid;
  assign to_pulp_req.r_ready    = slv_r_ready_i;

  assign rab_conf_req.aw.addr   = rab_conf_aw_addr_i;
  assign rab_conf_req.aw.prot   = rab_conf_aw_prot_i;
  assign rab_conf_req.aw_valid  = rab_conf_aw_valid_i;
  assign rab_conf_aw_ready_o    = rab_conf_resp.aw_ready;
  assign rab_conf_req.w.data    = rab_conf_w_data_i;
  assign rab_conf_req.w.strb    = rab_conf_w_strb_i;
  assign rab_conf_req.w_valid   = rab_conf_w_valid_i;
  assign rab_conf_w_ready_o     = rab_conf_resp.w_ready;
  assign rab_conf_b_resp_o      = rab_conf_resp.b.resp;
  assign rab_conf_b_valid_o     = rab_conf_resp.b_valid;
  assign rab_conf_req.b_ready   = rab_conf_b_ready_i;
  assign rab_conf_req.ar.addr   = rab_conf_ar_addr_i;
  assign rab_conf_req.ar.prot   = rab_conf_ar_prot_i;
  assign rab_conf_req.ar_valid  = rab_conf_ar_valid_i;
  assign rab_conf_ar_ready_o    = rab_conf_resp.ar_ready;
  assign rab_conf_r_data_o      = rab_conf_resp.r.data;
  assign rab_conf_r_resp_o      = rab_conf_resp.r.resp;
  assign rab_conf_r_valid_o     = rab_conf_resp.r_valid;
  assign rab_conf_req.r_ready   = rab_conf_r_ready_i;

  pulp #(
    .N_CLUSTERS       (N_CLUSTERS),
    .AXI_DW           (AXI_DW),
    .L2_N_AXI_PORTS   (L2_N_AXI_PORTS),
    .axi_req_t        (req_t),
    .axi_resp_t       (resp_t),
    .axi_lite_req_t   (lite_req_t),
    .axi_lite_resp_t  (lite_resp_t)
  ) i_bound (
    .clk_i,
    .rst_ni,
    .cl_fetch_en_i,
    .cl_eoc_o,
    .cl_busy_o,
    .rab_from_pulp_miss_irq_o,
    .rab_from_pulp_multi_irq_o,
    .rab_from_pulp_prot_irq_o,
    .rab_from_host_miss_irq_o,
    .rab_from_host_multi_irq_o,
    .rab_from_host_prot_irq_o,
    .rab_miss_fifo_full_irq_o,
    .mbox_irq_o,
    .ext_req_o        (from_pulp_req),
    .ext_resp_i       (from_pulp_resp),
    .ext_req_i        (to_pulp_req),
    .ext_resp_o       (to_pulp_resp),
    .rab_conf_req_i   (rab_conf_req),
    .rab_conf_resp_o  (rab_conf_resp)
  );

endmodule
