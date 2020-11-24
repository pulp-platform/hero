module snitch_cluster_synth_fixture import snitch_axi_pkg::*; (
  input  logic        clk_i,
  input  logic        rst_i,

  output id_slv_t     out_aw_id_o,
  output addr_t       out_aw_addr_o,
  output logic [7:0]  out_aw_len_o,
  output logic [2:0]  out_aw_size_o,
  output logic [1:0]  out_aw_burst_o,
  output logic        out_aw_lock_o,
  output logic [5:0]  out_aw_atop_o,
  output logic        out_aw_valid_o,
  input  logic        out_aw_ready_i,
  output data_t       out_w_data_o,
  output strb_t       out_w_strb_o,
  output logic        out_w_last_o,
  output logic        out_w_valid_o,
  input  logic        out_w_ready_i,
  input  id_slv_t     out_b_id_i,
  input  logic [1:0]  out_b_resp_i,
  input  logic        out_b_valid_i,
  output logic        out_b_ready_o,
  output id_slv_t     out_ar_id_o,
  output addr_t       out_ar_addr_o,
  output logic [7:0]  out_ar_len_o,
  output logic [2:0]  out_ar_size_o,
  output logic [1:0]  out_ar_burst_o,
  output logic        out_ar_lock_o,
  output logic        out_ar_valid_o,
  input  logic        out_ar_ready_i,
  input  id_slv_t     out_r_id_i,
  input  data_t       out_r_data_i,
  input  logic [1:0]  out_r_resp_i,
  input  logic        out_r_last_i,
  input  logic        out_r_valid_i,
  output logic        out_r_ready_o,

  input  id_t         in_aw_id_i,
  input  addr_t       in_aw_addr_i,
  input  logic [7:0]  in_aw_len_i,
  input  logic [2:0]  in_aw_size_i,
  input  logic [1:0]  in_aw_burst_i,
  input  logic        in_aw_lock_i,
  input  logic [5:0]  in_aw_atop_i,
  input  logic        in_aw_valid_i,
  output logic        in_aw_ready_o,
  input  data_t       in_w_data_i,
  input  strb_t       in_w_strb_i,
  input  logic        in_w_last_i,
  input  logic        in_w_valid_i,
  output logic        in_w_ready_o,
  output id_t         in_b_id_o,
  output logic [1:0]  in_b_resp_o,
  output logic        in_b_valid_o,
  input  logic        in_b_ready_i,
  input  id_t         in_ar_id_i,
  input  addr_t       in_ar_addr_i,
  input  logic [7:0]  in_ar_len_i,
  input  logic [2:0]  in_ar_size_i,
  input  logic [1:0]  in_ar_burst_i,
  input  logic        in_ar_lock_i,
  input  logic        in_ar_valid_i,
  output logic        in_ar_ready_o,
  output id_t         in_r_id_o,
  output data_t       in_r_data_o,
  output logic [1:0]  in_r_resp_o,
  output logic        in_r_last_o,
  output logic        in_r_valid_o,
  input  logic        in_r_ready_i,

  output id_dma_slv_t dma_aw_id_o,
  output addr_dma_t   dma_aw_addr_o,
  output logic [7:0]  dma_aw_len_o,
  output logic [2:0]  dma_aw_size_o,
  output logic [1:0]  dma_aw_burst_o,
  output logic        dma_aw_lock_o,
  output logic [5:0]  dma_aw_atop_o,
  output logic        dma_aw_valid_o,
  input  logic        dma_aw_ready_i,
  output data_dma_t   dma_w_data_o,
  output strb_dma_t   dma_w_strb_o,
  output logic        dma_w_last_o,
  output logic        dma_w_valid_o,
  input  logic        dma_w_ready_i,
  input  id_dma_slv_t dma_b_id_i,
  input  logic [1:0]  dma_b_resp_i,
  input  logic        dma_b_valid_i,
  output logic        dma_b_ready_o,
  output id_dma_slv_t dma_ar_id_o,
  output addr_dma_t   dma_ar_addr_o,
  output logic [7:0]  dma_ar_len_o,
  output logic [2:0]  dma_ar_size_o,
  output logic [1:0]  dma_ar_burst_o,
  output logic        dma_ar_lock_o,
  output logic        dma_ar_valid_o,
  input  logic        dma_ar_ready_i,
  input  id_dma_slv_t dma_r_id_i,
  input  data_dma_t   dma_r_data_i,
  input  logic [1:0]  dma_r_resp_i,
  input  logic        dma_r_last_i,
  input  logic        dma_r_valid_i,
  output logic        dma_r_ready_o

);

  snitch_axi_pkg::req_t axi_slv_req;
  snitch_axi_pkg::resp_t axi_slv_res;
  snitch_axi_pkg::req_slv_t axi_mst_req;
  snitch_axi_pkg::resp_slv_t axi_mst_res;
  snitch_axi_pkg::req_dma_slv_t axi_dma_req;
  snitch_axi_pkg::resp_dma_slv_t axi_dma_resp;

  snitch_sdma_cluster #(
    .BootAddr       ( 32'h8001_0000              ),
    .NrCores        ( 8                          ),
    .CoresPerHive   ( 4                          ),
    .Topology       ( tcdm_interconnect_pkg::LIC ),
    .SDMA           ( 1                          )
  ) i_snitch_sdma_cluster (
    .clk_i           ( clk_i        ),
    .rst_i           ( rst_i        ),
    .hart_base_id_i  ( '0           ),
    .axi_slv_req_i   ( axi_slv_req  ), // External Master (Snitch Slave Port)
    .axi_slv_res_o   ( axi_slv_res  ), // External Master (Snitch Slave Port)
    .axi_mst_req_o   ( axi_mst_req  ), // External Slave (Snitch Master Port)
    .axi_mst_res_i   ( axi_mst_res  ), // External Slave (Snitch Master Port)
    .ext_dma_req_o   ( axi_dma_req  ),
    .ext_dma_resp_i  ( axi_dma_resp )
  );

    assign axi_slv_req.aw.id       = in_aw_id_i;
    assign axi_slv_req.aw.addr     = in_aw_addr_i;
    assign axi_slv_req.aw.len      = in_aw_len_i;
    assign axi_slv_req.aw.size     = in_aw_size_i;
    assign axi_slv_req.aw.burst    = in_aw_burst_i;
    assign axi_slv_req.aw.lock     = in_aw_lock_i;
    assign axi_slv_req.aw.cache    = '0;
    assign axi_slv_req.aw.prot     = '0;
    assign axi_slv_req.aw.qos      = '0;
    assign axi_slv_req.aw.region   = '0;
    assign axi_slv_req.aw.atop     = in_aw_atop_i;
    assign axi_slv_req.aw_valid    = in_aw_valid_i;
    assign in_aw_ready_o           = axi_slv_res.aw_ready;
    assign axi_slv_req.w.data      = in_w_data_i;
    assign axi_slv_req.w.strb      = in_w_strb_i;
    assign axi_slv_req.w.last      = in_w_last_i;
    assign axi_slv_req.w_valid     = in_w_valid_i;
    assign in_w_ready_o            = axi_slv_res.w_ready;
    assign in_b_id_o               = axi_slv_res.b.id;
    assign in_b_resp_o             = axi_slv_res.b.resp;
    assign in_b_valid_o            = axi_slv_res.b_valid;
    assign axi_slv_req.b_ready     = in_b_ready_i;
    assign axi_slv_req.ar.id       = in_ar_id_i;
    assign axi_slv_req.ar.addr     = in_ar_addr_i;
    assign axi_slv_req.ar.len      = in_ar_len_i;
    assign axi_slv_req.ar.size     = in_ar_size_i;
    assign axi_slv_req.ar.burst    = in_ar_burst_i;
    assign axi_slv_req.ar.lock     = in_ar_lock_i;
    assign axi_slv_req.ar.cache    = '0;
    assign axi_slv_req.ar.prot     = '0;
    assign axi_slv_req.ar.qos      = '0;
    assign axi_slv_req.ar.region   = '0;
    assign axi_slv_req.ar_valid    = in_ar_valid_i;
    assign in_ar_ready_o           = axi_slv_res.ar_ready;
    assign in_r_id_o               = axi_slv_res.r.id;
    assign in_r_data_o             = axi_slv_res.r.data;
    assign in_r_resp_o             = axi_slv_res.r.resp;
    assign in_r_last_o             = axi_slv_res.r.last;
    assign in_r_valid_o            = axi_slv_res.r_valid;
    assign axi_slv_req.r_ready     = in_r_ready_i;

    assign out_aw_id_o             = axi_mst_req.aw.id;
    assign out_aw_addr_o           = axi_mst_req.aw.addr;
    assign out_aw_len_o            = axi_mst_req.aw.len;
    assign out_aw_size_o           = axi_mst_req.aw.size;
    assign out_aw_burst_o          = axi_mst_req.aw.burst;
    assign out_aw_lock_o           = axi_mst_req.aw.lock;
    assign out_aw_atop_o           = axi_mst_req.aw.atop;
    assign out_aw_valid_o          = axi_mst_req.aw_valid;
    assign axi_mst_res.aw_ready    = out_aw_ready_i;
    assign out_w_data_o            = axi_mst_req.w.data;
    assign out_w_strb_o            = axi_mst_req.w.strb;
    assign out_w_last_o            = axi_mst_req.w.last;
    assign out_w_valid_o           = axi_mst_req.w_valid;
    assign axi_mst_res.w_ready     = out_w_ready_i;
    assign axi_mst_res.b.id        = out_b_id_i;
    assign axi_mst_res.b.resp      = out_b_resp_i;
    assign axi_mst_res.b_valid     = out_b_valid_i;
    assign out_b_ready_o           = axi_mst_req.b_ready;
    assign out_ar_id_o             = axi_mst_req.ar.id;
    assign out_ar_addr_o           = axi_mst_req.ar.addr;
    assign out_ar_len_o            = axi_mst_req.ar.len;
    assign out_ar_size_o           = axi_mst_req.ar.size;
    assign out_ar_burst_o          = axi_mst_req.ar.burst;
    assign out_ar_lock_o           = axi_mst_req.ar.lock;
    assign out_ar_valid_o          = axi_mst_req.ar_valid;
    assign axi_mst_res.ar_ready    = out_ar_ready_i;
    assign axi_mst_res.r.id        = out_r_id_i;
    assign axi_mst_res.r.data      = out_r_data_i;
    assign axi_mst_res.r.resp      = out_r_resp_i;
    assign axi_mst_res.r.last      = out_r_last_i;
    assign axi_mst_res.r_valid     = out_r_valid_i;
    assign out_r_ready_o           = axi_mst_req.r_ready;

    assign dma_aw_id_o             = axi_dma_req.aw.id;
    assign dma_aw_addr_o           = axi_dma_req.aw.addr;
    assign dma_aw_len_o            = axi_dma_req.aw.len;
    assign dma_aw_size_o           = axi_dma_req.aw.size;
    assign dma_aw_burst_o          = axi_dma_req.aw.burst;
    assign dma_aw_lock_o           = axi_dma_req.aw.lock;
    assign dma_aw_atop_o           = axi_dma_req.aw.atop;
    assign dma_aw_valid_o          = axi_dma_req.aw_valid;
    assign axi_dma_resp.aw_ready   = dma_aw_ready_i;
    assign dma_w_data_o            = axi_dma_req.w.data;
    assign dma_w_strb_o            = axi_dma_req.w.strb;
    assign dma_w_last_o            = axi_dma_req.w.last;
    assign dma_w_valid_o           = axi_dma_req.w_valid;
    assign axi_dma_resp.w_ready    = dma_w_ready_i;
    assign axi_dma_resp.b.id       = dma_b_id_i;
    assign axi_dma_resp.b.resp     = dma_b_resp_i;
    assign axi_dma_resp.b_valid    = dma_b_valid_i;
    assign dma_b_ready_o           = axi_dma_req.b_ready;
    assign dma_ar_id_o             = axi_dma_req.ar.id;
    assign dma_ar_addr_o           = axi_dma_req.ar.addr;
    assign dma_ar_len_o            = axi_dma_req.ar.len;
    assign dma_ar_size_o           = axi_dma_req.ar.size;
    assign dma_ar_burst_o          = axi_dma_req.ar.burst;
    assign dma_ar_lock_o           = axi_dma_req.ar.lock;
    assign dma_ar_valid_o          = axi_dma_req.ar_valid;
    assign axi_dma_resp.ar_ready   = dma_ar_ready_i;
    assign axi_dma_resp.r.id       = dma_r_id_i;
    assign axi_dma_resp.r.data     = dma_r_data_i;
    assign axi_dma_resp.r.resp     = dma_r_resp_i;
    assign axi_dma_resp.r.last     = dma_r_last_i;
    assign axi_dma_resp.r_valid    = dma_r_valid_i;
    assign dma_r_ready_o           = axi_dma_req.r_ready;

endmodule

