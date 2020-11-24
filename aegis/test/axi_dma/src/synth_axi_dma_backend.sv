`include "axi/typedef.svh"

module synth_axi_dma_backend #(
    parameter int unsigned  AddrWidth    = -1,
    parameter int unsigned  DataWidth    = -1,
    parameter int unsigned  IdWidth      = -1,
    parameter int unsigned  AxFifoDepth  = -1,
    parameter int unsigned  ReqFifoDepth = -1,
    parameter int unsigned  BufferDepth  = -1,
    parameter type          addr_t       = logic [AddrWidth-1:0],
    parameter type          data_t       = logic [DataWidth-1:0],
    parameter type          strb_t       = logic [DataWidth/8-1:0],
    parameter type          id_t         = logic [IdWidth-1:0],
    parameter type          user_t       = logic [0:0]
) (
    input  logic                     clk_i,
    input  logic                     rst_ni,

    output id_t                      axi_aw_id_o,
    output addr_t                    axi_aw_addr_o,
    output axi_pkg::len_t            axi_aw_len_o,
    output axi_pkg::size_t           axi_aw_size_o,
    output axi_pkg::burst_t          axi_aw_burst_o,
    output logic                     axi_aw_lock_o,
    output axi_pkg::cache_t          axi_aw_cache_o,
    output axi_pkg::prot_t           axi_aw_prot_o,
    output axi_pkg::qos_t            axi_aw_qos_o,
    output axi_pkg::region_t         axi_aw_region_o,
    output axi_pkg::atop_t           axi_aw_atop_o,
    output user_t                    axi_aw_user_o,
    output logic                     axi_aw_valid_o,
    input  logic                     axi_aw_ready_i,
    output data_t                    axi_w_data_o,
    output strb_t                    axi_w_strb_o,
    output logic                     axi_w_last_o,
    output user_t                    axi_w_user_o,
    output logic                     axi_w_valid_o,
    input  logic                     axi_w_ready_i,
    input  id_t                      axi_b_id_i,
    input  axi_pkg::resp_t           axi_b_resp_i,
    input  user_t                    axi_b_user_i,
    input  logic                     axi_b_valid_i,
    output logic                     axi_b_ready_o,
    output id_t                      axi_ar_id_o,
    output addr_t                    axi_ar_addr_o,
    output axi_pkg::len_t            axi_ar_len_o,
    output axi_pkg::size_t           axi_ar_size_o,
    output axi_pkg::burst_t          axi_ar_burst_o,
    output logic                     axi_ar_lock_o,
    output axi_pkg::cache_t          axi_ar_cache_o,
    output axi_pkg::prot_t           axi_ar_prot_o,
    output axi_pkg::qos_t            axi_ar_qos_o,
    output axi_pkg::region_t         axi_ar_region_o,
    output user_t                    axi_ar_user_o,
    output logic                     axi_ar_valid_o,
    input  logic                     axi_ar_ready_i,
    input  id_t                      axi_r_id_i,
    input  data_t                    axi_r_data_i,
    input  axi_pkg::resp_t           axi_r_resp_i,
    input  logic                     axi_r_last_i,
    input  user_t                    axi_r_user_i,
    input  logic                     axi_r_valid_i,
    output logic                     axi_r_ready_o,

    input  id_t                      burst_req_id_i,
    input  addr_t                    burst_req_src_i,
    input  addr_t                    burst_req_dst_i,
    input  addr_t                    burst_req_num_bytes_i,
    input  axi_pkg::cache_t          burst_req_cache_src_i,
    input  axi_pkg::cache_t          burst_req_cache_dst_i,
    input  axi_pkg::burst_t          burst_req_burst_src_i,
    input  axi_pkg::burst_t          burst_req_burst_dst_i,
    input  logic                     burst_req_decouple_rw_i,
    input  logic                     burst_req_deburst_i,
    input  logic                     burst_valid_i,
    output logic                     burst_ready_o,

    output logic                     backend_idle_o,
    output logic                     trans_complete_o
);


    `AXI_TYPEDEF_AW_CHAN_T(aw_t, addr_t, id_t, user_t)
    `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
    `AXI_TYPEDEF_B_CHAN_T(b_t, id_t, user_t)
    `AXI_TYPEDEF_AR_CHAN_T(ar_t, addr_t, id_t, user_t)
    `AXI_TYPEDEF_R_CHAN_T(r_t, data_t, id_t, user_t)
    `AXI_TYPEDEF_REQ_T(req_t, aw_t, w_t, ar_t)
    `AXI_TYPEDEF_RESP_T(rsp_t, b_t, r_t)

    typedef struct packed {
        id_t             id;
        addr_t           src, dst, num_bytes;
        axi_pkg::cache_t cache_src, cache_dst;
        axi_pkg::burst_t burst_src, burst_dst;
        logic            decouple_rw;
        logic            deburst;
    } burst_req_t;

    req_t       axi_req;
    rsp_t       axi_rsp;
    burst_req_t burst_req;


    axi_dma_backend #(
        .DataWidth           ( DataWidth     ),
        .AddrWidth           ( AddrWidth     ),
        .IdWidth             ( IdWidth       ),
        .AxReqFifoDepth      ( AxFifoDepth   ),
        .TransFifoDepth      ( ReqFifoDepth  ),
        .BufferDepth         ( BufferDepth   ),
        .axi_req_t           ( req_t         ),
        .axi_res_t           ( rsp_t         ),
        .burst_req_t         ( burst_req_t   ),
        .DmaIdWidth          ( 0             ),
        .DmaTracing          ( 0             )
    ) i_axi_dma_backend (
        .clk_i               ( clk_i             ),
        .rst_ni              ( rst_ni            ),
        .axi_dma_req_o       ( axi_req           ),
        .axi_dma_res_i       ( axi_rsp           ),
        .burst_req_i         ( burst_req         ),
        .valid_i             ( burst_valid_i     ),
        .ready_o             ( burst_ready_o     ),
        .backend_idle_o      ( backend_idle_o    ),
        .trans_complete_o    ( trans_complete_o  ),
        .dma_id_i            ( '0                )
    );


    assign axi_aw_id_o        = axi_req.aw.id;
    assign axi_aw_addr_o      = axi_req.aw.addr;
    assign axi_aw_len_o       = axi_req.aw.len;
    assign axi_aw_size_o      = axi_req.aw.size;
    assign axi_aw_burst_o     = axi_req.aw.burst;
    assign axi_aw_lock_o      = axi_req.aw.lock;
    assign axi_aw_cache_o     = axi_req.aw.cache;
    assign axi_aw_prot_o      = axi_req.aw.prot;
    assign axi_aw_qos_o       = axi_req.aw.qos;
    assign axi_aw_region_o    = axi_req.aw.region;
    assign axi_aw_atop_o      = axi_req.aw.atop;
    assign axi_aw_user_o      = axi_req.aw.user;
    assign axi_aw_valid_o     = axi_req.aw_valid;
    assign axi_rsp.aw_ready   = axi_aw_ready_i;
    assign axi_w_data_o       = axi_req.w.data;
    assign axi_w_strb_o       = axi_req.w.strb;
    assign axi_w_last_o       = axi_req.w.last;
    assign axi_w_user_o       = axi_req.w.user;
    assign axi_w_valid_o      = axi_req.w_valid;
    assign axi_rsp.w_ready    = axi_w_ready_i;
    assign axi_rsp.b.id       = axi_b_id_i;
    assign axi_rsp.b.resp     = axi_b_resp_i;
    assign axi_rsp.b.user     = axi_b_user_i;
    assign axi_rsp.b_valid    = axi_b_valid_i;
    assign axi_b_ready_o      = axi_req.b_ready;
    assign axi_ar_id_o        = axi_req.ar.id;
    assign axi_ar_addr_o      = axi_req.ar.addr;
    assign axi_ar_len_o       = axi_req.ar.len;
    assign axi_ar_size_o      = axi_req.ar.size;
    assign axi_ar_burst_o     = axi_req.ar.burst;
    assign axi_ar_lock_o      = axi_req.ar.lock;
    assign axi_ar_cache_o     = axi_req.ar.cache;
    assign axi_ar_prot_o      = axi_req.ar.prot;
    assign axi_ar_qos_o       = axi_req.ar.qos;
    assign axi_ar_region_o    = axi_req.ar.region;
    assign axi_ar_user_o      = axi_req.ar.user;
    assign axi_ar_valid_o     = axi_req.ar_valid;
    assign axi_rsp.ar_ready   = axi_ar_ready_i;
    assign axi_rsp.r.id       = axi_r_id_i;
    assign axi_rsp.r.data     = axi_r_data_i;
    assign axi_rsp.r.resp     = axi_r_resp_i;
    assign axi_rsp.r.last     = axi_r_last_i;
    assign axi_rsp.r.user     = axi_r_user_i;
    assign axi_rsp.r_valid    = axi_r_valid_i;
    assign axi_r_ready_o      = axi_req.r_ready;
 
    assign burst_req.id           = burst_req_id_i;
    assign burst_req.src          = burst_req_src_i;
    assign burst_req.dst          = burst_req_dst_i;
    assign burst_req.num_bytes    = burst_req_num_bytes_i;
    assign burst_req.cache_src    = burst_req_cache_src_i;
    assign burst_req.cache_dst    = burst_req_cache_dst_i;
    assign burst_req.burst_src    = burst_req_burst_src_i;
    assign burst_req.burst_dst    = burst_req_burst_dst_i;
    assign burst_req.decouple_rw  = burst_req_decouple_rw_i;
    assign burst_req.deburst      = burst_req_deburst_i;
    
endmodule : synth_axi_dma_backend
