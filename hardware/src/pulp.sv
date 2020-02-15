// Copyright 2019 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

// This package makes internal constants of PULP accessible, e.g., in test environments.  Do not use
// these values to hierarchically design your system, though.


`include "axi/assign.svh"
`include "axi/typedef.svh"

package automatic pulp_pkg;

  // Addressing
  localparam int unsigned AXI_AW = pulp_cluster_cfg_pkg::AXI_AW;
  // Clusters
  localparam int unsigned AXI_DW_CL = pulp_cluster_cfg_pkg::AXI_DW;
  localparam int unsigned AXI_IW_CL_OUP = pulp_cluster_cfg_pkg::AXI_IW_MST;
  localparam int unsigned AXI_IW_CL_INP = pulp_cluster_cfg_pkg::AXI_IW_SLV;
  // SoC Bus
  localparam int unsigned AXI_IW_SB_INP = AXI_IW_CL_OUP;
  localparam int unsigned AXI_UW = pulp_cluster_cfg_pkg::AXI_UW;
  localparam int unsigned AXI_DW = 128;
  function int unsigned axi_iw_sb_oup(input int unsigned n_clusters);
    return soc_bus_pkg::oup_id_w(n_clusters, AXI_IW_SB_INP);
  endfunction
  // L2 Memory
  localparam int unsigned L2_SIZE = pulp_cluster_cfg_pkg::L2_SIZE;
  // localparam int unsigned L2_ATOMIC = 0;
  // Peripherals
  localparam int unsigned AXI_LITE_AW = 32;
  localparam int unsigned AXI_LITE_DW = 64;
  // AXI Interface Types
  typedef logic [AXI_AW-1:0]        addr_t;
  typedef logic [AXI_IW_SB_INP-1:0] id_slv_t;
  typedef logic [AXI_UW-1:0]        user_t;
  // AXI-Lite Interface Types
  typedef logic [AXI_LITE_AW-1:0]   lite_addr_t;
  typedef logic [AXI_LITE_DW-1:0]   lite_data_t;
  typedef logic [AXI_LITE_DW/8-1:0] lite_strb_t;

  localparam int unsigned AXI_IW = axi_iw_sb_oup(1);
  localparam int unsigned AXI_SW = 128/8;  // width of strobe
  typedef addr_t                axi_addr_t;
  typedef logic [AXI_DW-1:0]    axi_data_t;
  typedef logic [AXI_IW-1:0]    axi_id_t;
  typedef logic [AXI_SW-1:0]    axi_strb_t;
  typedef user_t                axi_user_t;
  `AXI_TYPEDEF_AW_CHAN_T(       axi_aw_t,     axi_addr_t, axi_id_t, axi_user_t);
  `AXI_TYPEDEF_W_CHAN_T(        axi_w_t,      axi_data_t, axi_strb_t, axi_user_t);
  `AXI_TYPEDEF_B_CHAN_T(        axi_b_t,      axi_id_t, axi_user_t);
  `AXI_TYPEDEF_AR_CHAN_T(       axi_ar_t,     axi_addr_t, axi_id_t, axi_user_t);
  `AXI_TYPEDEF_R_CHAN_T(        axi_r_t,      axi_data_t, axi_id_t, axi_user_t);
  `AXI_TYPEDEF_REQ_T(           axi_req_t,    axi_aw_t, axi_w_t, axi_ar_t);
  `AXI_TYPEDEF_RESP_T(          axi_resp_t,   axi_b_t, axi_r_t);

  // Debug module
  localparam logic [31:0] JTAG_IDCODE = 32'h249511C3; //TODO: do we have a sane value for this?
  localparam int unsigned N_DEBUG = 1;
  // localparam int unsigned AXI_IW_DEBUG = 1;
endpackage

import pulp_pkg::*;

module pulp #(
  // SoC Parameters
  parameter int unsigned  N_CLUSTERS = 1,           // must be a power of 2
  parameter int unsigned  AXI_DW = 128,             // [bit]
  parameter int unsigned  L2_N_AXI_PORTS = 1,       // must be a power of 2
  parameter type          axi_req_t = axi_req_t,
  parameter type          axi_resp_t = axi_resp_t,
  parameter type          axi_lite_req_t = logic,
  parameter type          axi_lite_resp_t = logic
) (
  // Clocks and Resets
  input  logic                  clk_i,
  input  logic                  rst_ni,

  // Cluster Control
  input  logic [N_CLUSTERS-1:0] cl_fetch_en_i,
  output logic [N_CLUSTERS-1:0] cl_eoc_o,
  output logic [N_CLUSTERS-1:0] cl_busy_o,

  output axi_req_t              ext_req_o,
  input  axi_resp_t             ext_resp_i,
  input  axi_req_t              ext_req_i,
  output axi_resp_t             ext_resp_o,

  //JTAG
  input  logic                  jtag_tck_i,
  input  logic                  jtag_trst_ni,
  input  logic                  jtag_tdi_i,
  input  logic                  jtag_tms_i,
  output logic                  jtag_tdo_o
);

  // Derived Constants
  localparam int unsigned N_SLAVES = soc_bus_pkg::n_slaves(N_CLUSTERS) + N_DEBUG;
  localparam int unsigned AXI_IW_SB_OUP = axi_iw_sb_oup(N_SLAVES);
  localparam int unsigned NR_HARTS = N_CLUSTERS * pulp_cluster_cfg_pkg::N_CORES;


  // maximum hartid in system
  // we have the following hartspace:
  // logic [5:0] cluster_id = 0...N_CLUSTERS-1
  // logic [3:0] core_id = 0...N_CORES-1
  // mhartid = {21'b0, cluster_id_i[5:0], 1'b0, core_id_i[3:0]}
  localparam logic [31:0] DM_MAX_HARTS = ((N_CLUSTERS-1) << 5) | 32'(pulp_cluster_cfg_pkg::N_CORES);

  // debug signals
  logic [DM_MAX_HARTS-1:0] core_debug_req;

  // Interfaces to Clusters
  // i_soc_bus.cl_mst -> [cl_inp]
  // -> i_id_remap_cl_inp -> [cl_inp_remapped]
  // -> i_dwc_cl_inp -> [cl_inp_dwced]
  // if async:  -> i_dc_slice_cl_inp -> [cl_inp_async]
  // else:      -> i_cluster.data_slave
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (AXI_UW)
  ) cl_inp[N_CLUSTERS-1:0]();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_CL_INP),
    .AXI_USER_WIDTH (AXI_UW)
  ) cl_inp_remapped[N_CLUSTERS-1:0]();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW_CL),
    .AXI_ID_WIDTH   (AXI_IW_CL_INP),
    .AXI_USER_WIDTH (AXI_UW)
  ) cl_inp_dwced[N_CLUSTERS-1:0]();
  AXI_BUS_ASYNC #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW_CL),
    .AXI_ID_WIDTH   (AXI_IW_CL_INP),
    .AXI_USER_WIDTH (AXI_UW),
    .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
  ) cl_inp_async[N_CLUSTERS-1:0]();

  // Interfaces from Clusters
  // if async:  i_cluster.data_master.* -> [cl_oup_async] -> i_dc_slice_cl_oup -> [cl_oup_predwc]
  // else:      i_cluster.data_master.* -> [cl_oup_predwc]
  // -> i_dwc_cl_oup -> [cl_oup_prebuf]
  // -> i_r_buf_cl_oup -> [cl_oup]
  // -> i_soc_bus.cl_slv
  AXI_BUS_ASYNC #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW_CL),
    .AXI_ID_WIDTH   (AXI_IW_CL_OUP),
    .AXI_USER_WIDTH (AXI_UW),
    .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
  ) cl_oup_async[N_CLUSTERS-1:0]();
  // pragma translate_off
  initial assert (AXI_IW_CL_OUP == AXI_IW_SB_INP);
  // pragma translate_on
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW_CL),
    .AXI_ID_WIDTH   (AXI_IW_SB_INP),
    .AXI_USER_WIDTH (AXI_UW)
  ) cl_oup_predwc[N_CLUSTERS-1:0]();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_INP),
    .AXI_USER_WIDTH (AXI_UW)
  ) cl_oup_prebuf[N_CLUSTERS-1:0]();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_INP),
    .AXI_USER_WIDTH (AXI_UW)
  ) cl_oup[N_CLUSTERS-1:0]();

  // Interfaces to L2 Memory
  // i_soc_bus.l2_mst -> [l2_mst]
  // -> i_atomics -> [l2_mst_wo_atomics]
  // -> i_l2_mem.slv
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (AXI_UW)
  ) l2_mst[L2_N_AXI_PORTS-1:0]();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (AXI_UW)
  ) l2_mst_wo_atomics[L2_N_AXI_PORTS-1:0]();

  // Interfaces from PULP to Host
  // i_soc_bus.ext_mst -> [ext_mst]
  // -> i_atop_filter -> [ext_mst_atop_filtered]
  // -> [ext_{req_o,resp_i}]
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (AXI_UW)
  ) ext_mst();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (AXI_UW)
  ) ext_mst_atop_filtered();
  `AXI_ASSIGN_TO_REQ(ext_req_o, ext_mst_atop_filtered);
  `AXI_ASSIGN_FROM_RESP(ext_mst_atop_filtered, ext_resp_i);

  // Interfaces from Host to PULP
  // [ext_{req_i,resp_o}] -> [ext_slv]
  // -> i_id_remap_ext_slv -> [ext_slv_remapped]
  // -> i_soc_bus.ext_slv
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (AXI_UW)
  ) ext_slv();
  `AXI_ASSIGN_FROM_REQ(ext_slv, ext_req_i);
  `AXI_ASSIGN_TO_RESP(ext_resp_o, ext_slv);
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_INP),
    .AXI_USER_WIDTH (AXI_UW)
  ) ext_slv_remapped();

  // Interfaces to Peripherals
  // i_soc_bus.periph_mst -> [periph_mst]
  // -> i_dwc_periph_mst -> [periph_mst_dwced]
  // -> i_periphs.axi
  localparam int unsigned AXI_DW_PERIPHS = 64;
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (AXI_UW)
  ) periph_mst();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW_PERIPHS),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (AXI_UW)
  ) periph_mst_dwced();

  // Interface from debug module to soc bus
  // i_debug_system.dm_master -> [debug_mst_predwc]
  // -> i_dwc_debug_mst -> [debug_mst_dwced]
  // -> i_soc_bus.debug_slv
  // we don't really support anything else than 32 bits for now
  localparam int unsigned AXI_DW_DM = 32;
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW_DM),
    .AXI_ID_WIDTH   (AXI_IW_SB_INP),
    .AXI_USER_WIDTH (AXI_UW)
  ) debug_mst_predwc();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_INP),
    .AXI_USER_WIDTH (AXI_UW)
  ) debug_mst_dwced();

   AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (AXI_UW)
  ) debug_slv_predwc();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW_DM),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (AXI_UW)
  ) debug_slv_dwced();

  for (genvar i = 0; i < N_CLUSTERS; i++) begin: gen_clusters
    axi_id_resize #(
      .ADDR_WIDTH   (AXI_AW),
      .DATA_WIDTH   (AXI_DW),
      .USER_WIDTH   (AXI_UW),
      .ID_WIDTH_IN  (AXI_IW_SB_OUP),
      .ID_WIDTH_OUT (AXI_IW_CL_INP),
      .TABLE_SIZE   (4)
    ) i_id_resize_cl_inp (
      .clk_i,
      .rst_ni,
      .in     (cl_inp[i]),
      .out    (cl_inp_remapped[i])
    );

    axi_data_width_converter #(
      .ADDR_WIDTH     (AXI_AW),
      .SI_DATA_WIDTH  (AXI_DW),
      .MI_DATA_WIDTH  (AXI_DW_CL),
      .ID_WIDTH       (AXI_IW_CL_INP),
      .USER_WIDTH     (AXI_UW)
    ) i_dwc_cl_inp (
      .clk_i,
      .rst_ni,
      .slv    (cl_inp_remapped[i]),
      .mst    (cl_inp_dwced[i])
    );

    logic [5:0] cluster_id;
    assign cluster_id = i;

    localparam int unsigned N_CORES = pulp_cluster_cfg_pkg::N_CORES;
    if (pulp_cluster_cfg_pkg::ASYNC) begin : gen_cluster_async

      axi_slice_dc_slave_wrap #(
        .AXI_ADDR_WIDTH (AXI_AW),
        .AXI_DATA_WIDTH (AXI_DW_CL),
        .AXI_USER_WIDTH (AXI_UW),
        .AXI_ID_WIDTH   (AXI_IW_CL_INP),
        .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
      ) i_dc_slice_cl_inp (
        .clk_i,
        .rst_ni,
        .test_cgbypass_i  (1'b0),
        .isolate_i        (1'b0),
        .axi_slave        (cl_inp_dwced[i]),
        .axi_master_async (cl_inp_async[i])
      );
      pulp_cluster_async i_cluster (
        .clk_i,
        .rst_ni,
        .ref_clk_i    (clk_i),
        .cluster_id_i (cluster_id),
        .fetch_en_i   (cl_fetch_en_i[i]),
        .eoc_o        (cl_eoc_o[i]),
        .busy_o       (cl_busy_o[i]),
        .dbg_irq_i    (core_debug_req[(i << 5) +: N_CORES]),
        .slv          (cl_inp_async[i]),
        .mst          (cl_oup_async[i])
      );
      axi_slice_dc_master_wrap #(
        .AXI_ADDR_WIDTH (AXI_AW),
        .AXI_DATA_WIDTH (AXI_DW_CL),
        .AXI_USER_WIDTH (AXI_UW),
        .AXI_ID_WIDTH   (AXI_IW_CL_OUP),
        .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
      ) i_dc_slice_cl_oup (
        .clk_i,
        .rst_ni,
        .test_cgbypass_i  (1'b0),
        .clock_down_i     (1'b0),
        .isolate_i        (1'b0),
        .incoming_req_o   (),
        .axi_slave_async  (cl_oup_async[i]),
        .axi_master       (cl_oup_predwc[i])
      );

    end else begin : gen_cluster_sync

      pulp_cluster_sync i_cluster (
        .clk_i,
        .rst_ni,
        .ref_clk_i    (clk_i),
        .cluster_id_i (cluster_id),
        .fetch_en_i   (cl_fetch_en_i[i]),
        .eoc_o        (cl_eoc_o[i]),
        .busy_o       (cl_busy_o[i]),
        .dbg_irq_i    (core_debug_req[(i << 5) +: N_CORES]),
        .slv          (cl_inp_dwced[i]),
        .mst          (cl_oup_predwc[i])
      );
    end

    axi_data_width_converter #(
      .ADDR_WIDTH     (AXI_AW),
      .SI_DATA_WIDTH  (AXI_DW_CL),
      .MI_DATA_WIDTH  (AXI_DW),
      .ID_WIDTH       (AXI_IW_CL_OUP),
      .USER_WIDTH     (AXI_UW),
      .NR_OUTSTANDING (8)
    ) i_dwc_cl_oup (
      .clk_i,
      .rst_ni,
      .slv    (cl_oup_predwc[i]),
      .mst    (cl_oup_prebuf[i])
    );

    axi_read_burst_buffer_wrap #(
      .ADDR_WIDTH   (AXI_AW),
      .DATA_WIDTH   (AXI_DW),
      .ID_WIDTH     (AXI_IW_CL_OUP),
      .USER_WIDTH   (AXI_UW),
      .BUF_DEPTH    (pulp_cluster_cfg_pkg::DMA_MAX_BURST_LEN)
    ) i_r_buf_cl_oup (
      .clk_i,
      .rst_ni,
      .slv    (cl_oup_prebuf[i]),
      .mst    (cl_oup[i])
    );
  end

  soc_bus #(
    .AXI_AW               (AXI_AW),
    .AXI_DW               (AXI_DW),
    .AXI_UW               (AXI_UW),
    .AXI_IW_INP           (AXI_IW_SB_INP),
    .N_CLUSTERS           (N_CLUSTERS),
    .L2_N_PORTS           (L2_N_AXI_PORTS),
    .L2_N_BYTES_PER_PORT  (L2_SIZE/L2_N_AXI_PORTS),
    .PERIPH_N_BYTES       (32*1024),
    .DEBUG_N_BYTES        (pulp_cluster_cfg_pkg::DM_SIZE),
    .DEBUG_BASE_ADDR      (64'(pulp_cluster_cfg_pkg::DM_BASE_ADDR)),
    .MST_SLICE_DEPTH      (1),
    .SLV_SLICE_DEPTH      (1)
  ) i_soc_bus (
    .clk_i,
    .rst_ni,
    .cl_slv     (cl_oup),
    .cl_mst     (cl_inp),
    .l2_mst     (l2_mst),
    .ext_mst    (ext_mst),
    .ext_slv    (ext_slv_remapped),
    .debug_slv  (debug_mst_dwced),
    .debug_mst  (debug_slv_predwc)
  );

  axi_atop_filter_intf #(
    .AXI_ID_WIDTH       (AXI_IW),
    .AXI_ADDR_WIDTH     (AXI_AW),
    .AXI_DATA_WIDTH     (AXI_DW),
    .AXI_USER_WIDTH     (AXI_UW),
    .AXI_MAX_WRITE_TXNS (N_CLUSTERS * pulp_cluster_cfg_pkg::DMA_MAX_N_TXNS)
  ) i_atop_filter (
    .clk_i,
    .rst_ni,
    .slv  (ext_mst),
    .mst  (ext_mst_atop_filtered)
  );

  for (genvar i = 0; i < L2_N_AXI_PORTS; i++) begin: gen_l2_ports
    // if (L2_ATOMIC) begin
    //   axi_riscv_atomics_wrap #(
    //     .AXI_ADDR_WIDTH     (AXI_AW),
    //     .AXI_DATA_WIDTH     (AXI_DW),
    //     .AXI_ID_WIDTH       (AXI_IW_SB_OUP),
    //     .AXI_USER_WIDTH     (AXI_UW),
    //     .AXI_MAX_READ_TXNS  (4),
    //     .AXI_MAX_WRITE_TXNS (4),
    //     .RISCV_WORD_WIDTH   (32)
    //   ) i_atomics (
    //     .clk_i,
    //     .rst_ni,
    //     .slv    (l2_mst[i]),
    //     .mst    (l2_mst_wo_atomics[i])
    //   );

    //   l2_mem #(
    //     .AXI_AW     (AXI_AW),
    //     .AXI_DW     (AXI_DW),
    //     .AXI_UW     (AXI_UW),
    //     .AXI_IW     (AXI_IW_SB_OUP),
    //     .N_BYTES    (L2_SIZE/L2_N_AXI_PORTS)
    //   ) i_l2_mem (
    //     .clk_i,
    //     .rst_ni,
    //     .slv    (l2_mst_wo_atomics[i])
    //   );
    // end else begin
      l2_mem #(
        .AXI_AW     (AXI_AW),
        .AXI_DW     (AXI_DW),
        .AXI_UW     (AXI_UW),
        .AXI_IW     (AXI_IW_SB_OUP),
        .N_BYTES    (L2_SIZE/L2_N_AXI_PORTS)
      ) i_l2_mem (
        .clk_i,
        .rst_ni,
        .slv    (l2_mst[i])
      );
    // end
  end

  axi_id_resize #(
    .ADDR_WIDTH   (AXI_AW),
    .DATA_WIDTH   (AXI_DW),
    .USER_WIDTH   (AXI_UW),
    .ID_WIDTH_IN  (AXI_IW_SB_OUP),
    .ID_WIDTH_OUT (AXI_IW_SB_INP),
    .TABLE_SIZE   (4)
  ) i_id_resize_ext_slv (
    .clk_i,
    .rst_ni,
    .in     (ext_slv),
    .out    (ext_slv_remapped)
  );

  axi_data_width_converter #(
    .ADDR_WIDTH     (AXI_AW),
    .SI_DATA_WIDTH  (AXI_DW),
    .MI_DATA_WIDTH  (AXI_DW_PERIPHS),
    .ID_WIDTH       (AXI_IW_SB_OUP),
    .USER_WIDTH     (AXI_UW)
  ) i_dwc_periph_mst (
    .clk_i,
    .rst_ni,
    .slv    (periph_mst),
    .mst    (periph_mst_dwced)
  );

  axi_data_width_converter #(
    .ADDR_WIDTH     (AXI_AW),
    .SI_DATA_WIDTH  (AXI_DW_DM),
    .MI_DATA_WIDTH  (AXI_DW),
    .ID_WIDTH       (AXI_IW_SB_INP),
    .USER_WIDTH     (AXI_UW),
    .NR_OUTSTANDING (1)
  ) i_dwc_debug_mst (
    .clk_i,
    .rst_ni,
    .slv    (debug_mst_predwc),
    .mst    (debug_mst_dwced)
  );

  axi_data_width_converter #(
    .ADDR_WIDTH     (AXI_AW),
    .SI_DATA_WIDTH  (AXI_DW),
    .MI_DATA_WIDTH  (AXI_DW_DM),
    .ID_WIDTH       (AXI_IW_SB_OUP),
    .USER_WIDTH     (AXI_UW),
    .NR_OUTSTANDING (1)
  ) i_dwc_debug_slv (
    .clk_i,
    .rst_ni,
    .slv    (debug_slv_predwc),
    .mst    (debug_slv_dwced)
  );

  debug_system #(
    .AXI_AW (AXI_AW),
    .AXI_DW (AXI_DW_DM),
    .AXI_IW (AXI_IW_SB_INP),
    .AXI_UW (AXI_UW),
    .JTAG_IDCODE (JTAG_IDCODE),
    .N_CORES (pulp_cluster_cfg_pkg::N_CORES),
    .N_CLUSTERS (N_CLUSTERS),
    .MAX_HARTS (DM_MAX_HARTS)
  ) i_debug_system (
    .clk_i,
    .rst_ni,
    .test_en_i        ('0),
    .jtag_tck_i,
    .jtag_trst_ni,
    .jtag_tdi_i,
    .jtag_tms_i,
    .jtag_tdo_o,
    .core_debug_req_o (core_debug_req),
    .dm_slave         (debug_slv_dwced),
    .dm_master        (debug_mst_predwc)
  );

  soc_peripherals #(
    .AXI_AW     (AXI_AW),
    .AXI_IW     (AXI_IW_SB_OUP),
    .AXI_UW     (AXI_UW),
    .N_CORES    (pulp_cluster_cfg_pkg::N_CORES),
    .N_CLUSTERS (N_CLUSTERS)
  ) i_periphs (
    .clk_i,
    .rst_ni,
    .test_en_i  ('0),
    .axi        (periph_mst_dwced)
  );

endmodule
