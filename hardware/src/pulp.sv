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

// This package makes internal constants of PULP accessible, e.g., in test environments.  Do not use
// these values to hierarchically design your system, though.


`include "assign.svh"
`include "typedef.svh"

package pulp_pkg;

  // Addressing
  localparam int unsigned AXI_AW = pulp_cluster_cfg_pkg::AXI_AW;
  // Clusters
  localparam int unsigned AXI_DW_CL = pulp_cluster_cfg_pkg::AXI_DW;
  localparam int unsigned AXI_IW_CL_OUP = pulp_cluster_cfg_pkg::AXI_IW_MST;
  localparam int unsigned AXI_IW_CL_INP = pulp_cluster_cfg_pkg::AXI_IW_SLV;
  // If this is set, clusters must never apply atomic operations (ATOPs) at their AXI master port.
  localparam logic CL_OUP_NO_ATOP = 1'b1;
  // SoC Bus
  localparam int unsigned AXI_IW_SB_INP = AXI_IW_CL_OUP;
  localparam int unsigned AXI_UW = pulp_cluster_cfg_pkg::AXI_UW;
  localparam int unsigned AXI_DW = 64;
  function automatic int unsigned axi_iw_sb_oup(input int unsigned n_clusters);
    return soc_bus_pkg::oup_id_w(n_clusters, AXI_IW_SB_INP);
  endfunction
  // L2 Memory
  localparam int unsigned L2_SIZE = pulp_cluster_cfg_pkg::L2_SIZE;
  // Peripherals
  localparam int unsigned AXI_LITE_AW = 32;
  localparam int unsigned AXI_LITE_DW = 64;
  // AXI Interface Types
  typedef logic [AXI_AW-1:0]        addr_t;
  typedef logic [AXI_UW-1:0]        user_t;
  // AXI-Lite Interface Types
  typedef logic [AXI_LITE_AW-1:0]   lite_addr_t;
  typedef logic [AXI_LITE_DW-1:0]   lite_data_t;
  typedef logic [AXI_LITE_DW/8-1:0] lite_strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(axi_lite_aw_t, lite_addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(axi_lite_w_t, lite_data_t, lite_strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(axi_lite_b_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(axi_lite_ar_t, lite_addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(axi_lite_r_t, lite_data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_lite_req_t, axi_lite_aw_t, axi_lite_w_t, axi_lite_ar_t)
  `AXI_LITE_TYPEDEF_RESP_T(axi_lite_resp_t, axi_lite_b_t, axi_lite_r_t)

  localparam int unsigned AXI_IW_MST = axi_iw_sb_oup(1);
  localparam int unsigned AXI_IW_SLV = 8;
  localparam int unsigned AXI_SW = AXI_DW/8;  // width of strobe
  typedef addr_t                  axi_addr_t;
  typedef logic [AXI_DW-1:0]      axi_data_t;
  typedef logic [AXI_IW_MST-1:0]  axi_id_mst_t;
  typedef logic [AXI_IW_SLV-1:0]  axi_id_slv_t;
  typedef logic [AXI_SW-1:0]      axi_strb_t;
  typedef user_t                  axi_user_t;
  `AXI_TYPEDEF_AW_CHAN_T(axi_aw_mst_t, axi_addr_t, axi_id_mst_t, axi_user_t)
  `AXI_TYPEDEF_AW_CHAN_T(axi_aw_slv_t, axi_addr_t, axi_id_slv_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(axi_w_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(axi_b_mst_t, axi_id_mst_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(axi_b_slv_t, axi_id_slv_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(axi_ar_mst_t, axi_addr_t, axi_id_mst_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(axi_ar_slv_t, axi_addr_t, axi_id_slv_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(axi_r_mst_t, axi_data_t, axi_id_mst_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(axi_r_slv_t, axi_data_t, axi_id_slv_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_mst_t, axi_aw_mst_t, axi_w_t, axi_ar_mst_t)
  `AXI_TYPEDEF_REQ_T(axi_req_slv_t, axi_aw_slv_t, axi_w_t, axi_ar_slv_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_mst_t, axi_b_mst_t, axi_r_mst_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_slv_t, axi_b_slv_t, axi_r_slv_t)

  // Debug module
  localparam logic [31:0] JTAG_IDCODE = 32'h249511C3; //TODO: do we have a sane value for this?
  localparam int unsigned N_DEBUG = 1;
  // localparam int unsigned AXI_IW_DEBUG = 1;
endpackage

module pulp #(
  // SoC Parameters
  parameter int unsigned  N_CLUSTERS = 1,           // must be a power of 2
  parameter int unsigned  L2_N_AXI_PORTS = 1        // must be a power of 2
) (
  // Clocks and Resets
  input  logic                    clk_i,
  input  logic                    rst_ni,

  // Cluster Control
  input  logic [N_CLUSTERS-1:0]   cl_fetch_en_i,
  output logic [N_CLUSTERS-1:0]   cl_eoc_o,
  output logic [N_CLUSTERS-1:0]   cl_busy_o,

  input  logic                    mailbox_evt_i, //mailbox event dedicated signal
  input  logic                    ext_evt_1_i,
  input  logic                    ext_evt_2_i,
  input  logic                    ext_evt_3_i,

  output pulp_pkg::axi_req_mst_t  ext_req_o,
  input  pulp_pkg::axi_resp_mst_t ext_resp_i,
  input  pulp_pkg::axi_req_slv_t  ext_req_i,
  output pulp_pkg::axi_resp_slv_t ext_resp_o,

  //JTAG
  input  logic                    jtag_tck_i,
  input  logic                    jtag_trst_ni,
  input  logic                    jtag_tdi_i,
  input  logic                    jtag_tms_i,
  output logic                    jtag_tdo_o,
  output logic                    jtag_tdo_en_o,

  // DFT (no direction suffixes due to partner request)
  input  logic [25:0]             mem_ctrl,
  input  logic                    dft_mode,
  input  logic                    dft_glb_gt_se,
  input  logic                    dft_ram_gt_se,
  input  logic                    dft_ram_bypass,
  input  logic                    dft_ram_bp_clk_en
);

  // Derived Constants
  localparam int unsigned N_SLAVES = soc_bus_pkg::n_slaves(N_CLUSTERS) + pulp_pkg::N_DEBUG;
  localparam int unsigned AXI_IW_SB_OUP = pulp_pkg::axi_iw_sb_oup(N_SLAVES);
  localparam int unsigned NR_HARTS = N_CLUSTERS * pulp_cluster_cfg_pkg::N_CORES;


  // maximum hartid in system
  // we have the following hartspace:
  // logic [5:0] cluster_id = 0...N_CLUSTERS-1
  // logic [3:0] core_id = 0...N_CORES-1
  // mhartid = {21'b0, cluster_id_i[5:0], 1'b0, core_id_i[3:0]}
  localparam logic [31:0] DM_MAX_HARTS = ((N_CLUSTERS-1) << 5) | 32'(pulp_cluster_cfg_pkg::N_CORES);

  // debug signals
  logic [DM_MAX_HARTS-1:0] core_debug_req;

  // non-debug module reset (synchronized)
  logic                    ndmreset_n;

  // Interfaces to Clusters
  // i_soc_bus.cl_mst -> [cl_inp]
  // -> i_id_remap_cl_inp -> [cl_inp_remapped]
  // -> i_dwc_cl_inp -> [cl_inp_dwced]
  // if async:  -> i_dc_slice_cl_inp -> [cl_inp_async]
  // else:      -> i_cluster.data_slave
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) cl_inp[N_CLUSTERS-1:0]();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW),
    .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_CL_INP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) cl_inp_remapped[N_CLUSTERS-1:0]();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW_CL),
    .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_CL_INP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) cl_inp_dwced[N_CLUSTERS-1:0]();
  AXI_BUS_ASYNC #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW_CL),
    .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_CL_INP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW),
    .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
  ) cl_inp_async[N_CLUSTERS-1:0]();

  // Interfaces from Clusters
  // if async:  i_cluster.data_master.* -> [cl_oup_async] -> i_dc_slice_cl_oup -> [cl_oup_prefilter]
  // else:      i_cluster.data_master.* -> [cl_oup_prefilter]
  // -> i_atop_filter_cl_oup -> [cl_oup_prebuf]
  // -> i_dwc_cl_oup -> [cl_oup_prebuf]
  // -> i_r_buf_cl_oup -> [cl_oup]
  // -> i_soc_bus.cl_slv
  AXI_BUS_ASYNC #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW_CL),
    .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_CL_OUP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW),
    .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
  ) cl_oup_async[N_CLUSTERS-1:0]();
  // pragma translate_off
  initial assert (pulp_pkg::AXI_IW_CL_OUP == pulp_pkg::AXI_IW_SB_INP);
  // pragma translate_on
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW_CL),
    .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_SB_INP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) cl_oup_prefilter[N_CLUSTERS-1:0]();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW_CL),
    .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_SB_INP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) cl_oup_predwc[N_CLUSTERS-1:0]();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW),
    .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_SB_INP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) cl_oup_prebuf[N_CLUSTERS-1:0]();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW),
    .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_SB_INP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) cl_oup[N_CLUSTERS-1:0]();

  // Interfaces to L2 Memory
  // i_soc_bus.l2_mst -> [l2_mst]
  // -> i_l2_mem.slv
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) l2_mst[L2_N_AXI_PORTS-1:0]();

  // Interfaces from PULP to Host
  // i_soc_bus.ext_mst -> [ext_mst] -> [ext_{req_o,resp_i}]
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) ext_mst();
  `AXI_ASSIGN_TO_REQ(ext_req_o, ext_mst)
  `AXI_ASSIGN_FROM_RESP(ext_mst, ext_resp_i)

  // Interfaces from Host to PULP
  // [ext_{req_i,resp_o}] -> [ext_slv]
  // -> i_id_remap_ext_slv -> [ext_slv_remapped]
  // -> i_soc_bus.ext_slv
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW),
    .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_SLV),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) ext_slv();
  `AXI_ASSIGN_FROM_REQ(ext_slv, ext_req_i)
  `AXI_ASSIGN_TO_RESP(ext_resp_o, ext_slv)
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW),
    .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_SB_INP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) ext_slv_remapped();

  // Interface from debug module to soc bus
  // i_debug_system.dm_master -> [debug_mst_predwc]
  // -> i_dwc_debug_mst -> [debug_mst_dwced]
  // -> i_soc_bus.debug_slv
  // we don't really support anything else than 32 bits for now
  localparam int unsigned AXI_DW_DM = 32;
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW_DM),
    .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_SB_INP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) debug_mst_predwc();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW),
    .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_SB_INP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) debug_mst_dwced();

   AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (pulp_pkg::AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) debug_slv_predwc();
  AXI_BUS #(
    .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW_DM),
    .AXI_ID_WIDTH   (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH (pulp_pkg::AXI_UW)
  ) debug_slv_dwced();

  for (genvar i = 0; i < N_CLUSTERS; i++) begin: gen_clusters
    axi_id_resize #(
      .ADDR_WIDTH   (pulp_pkg::AXI_AW),
      .DATA_WIDTH   (pulp_pkg::AXI_DW),
      .USER_WIDTH   (pulp_pkg::AXI_UW),
      .ID_WIDTH_IN  (AXI_IW_SB_OUP),
      .ID_WIDTH_OUT (pulp_pkg::AXI_IW_CL_INP),
      .TABLE_SIZE   (4)
    ) i_id_resize_cl_inp (
      .clk_i,
      .rst_ni (ndmreset_n),
      .in     (cl_inp[i]),
      .out    (cl_inp_remapped[i])
    );

    if (pulp_pkg::AXI_DW_CL != pulp_pkg::AXI_DW) begin : gen_dwc_cl_inp
      axi_dw_converter_intf #(
        .AXI_ADDR_WIDTH           (pulp_pkg::AXI_AW),
        .AXI_SLV_PORT_DATA_WIDTH  (pulp_pkg::AXI_DW),
        .AXI_MST_PORT_DATA_WIDTH  (pulp_pkg::AXI_DW_CL),
        .AXI_ID_WIDTH             (pulp_pkg::AXI_IW_CL_INP),
        .AXI_USER_WIDTH           (pulp_pkg::AXI_UW)
      ) i_dwc_cl_inp (
        .clk_i,
        .rst_ni (ndmreset_n),
        .slv    (cl_inp_remapped[i]),
        .mst    (cl_inp_dwced[i])
      );
    end else begin : gen_no_dwc_cl_inp
      `AXI_ASSIGN(cl_inp_dwced[i], cl_inp_remapped[i]);
    end

    logic [5:0] cluster_id;
    assign cluster_id = i;

    localparam int unsigned N_CORES = pulp_cluster_cfg_pkg::N_CORES;
    if (pulp_cluster_cfg_pkg::ASYNC) begin : gen_cluster_async

      axi_slice_dc_slave_wrap #(
        .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
        .AXI_DATA_WIDTH (pulp_pkg::AXI_DW_CL),
        .AXI_USER_WIDTH (pulp_pkg::AXI_UW),
        .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_CL_INP),
        .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
      ) i_dc_slice_cl_inp (
        .clk_i,
        .rst_ni (ndmreset_n),
        .test_cgbypass_i  (dft_glb_gt_se),
        .isolate_i        (1'b0),
        .axi_slave        (cl_inp_dwced[i]),
        .axi_master_async (cl_inp_async[i])
      );
      pulp_cluster_async i_cluster (
        .clk_i,
        .rst_ni (ndmreset_n),
        .ref_clk_i    (clk_i),
        .test_mode_i  (dft_glb_gt_se),
        .cluster_id_i (cluster_id),
        .fetch_en_i   (cl_fetch_en_i[i]),
        .eoc_o        (cl_eoc_o[i]),
        .busy_o       (cl_busy_o[i]),
        .dbg_irq_i    (core_debug_req[(i << 5) +: N_CORES]),
        .mailbox_evt_i,
        .ext_evt_1_i,
        .ext_evt_2_i,
        .ext_evt_3_i,
        .mem_ctrl,
        .dft_ram_gt_se,
        .dft_ram_bypass,
        .dft_ram_bp_clk_en,
        .slv          (cl_inp_async[i]),
        .mst          (cl_oup_async[i])
      );
      axi_slice_dc_master_wrap #(
        .AXI_ADDR_WIDTH (pulp_pkg::AXI_AW),
        .AXI_DATA_WIDTH (pulp_pkg::AXI_DW_CL),
        .AXI_USER_WIDTH (pulp_pkg::AXI_UW),
        .AXI_ID_WIDTH   (pulp_pkg::AXI_IW_CL_OUP),
        .BUFFER_WIDTH   (pulp_cluster_cfg_pkg::DC_BUF_W)
      ) i_dc_slice_cl_oup (
        .clk_i,
        .rst_ni (ndmreset_n),
        .test_cgbypass_i  (dft_glb_gt_se),
        .clock_down_i     (1'b0),
        .isolate_i        (1'b0),
        .incoming_req_o   (),
        .axi_slave_async  (cl_oup_async[i]),
        .axi_master       (cl_oup_prefilter[i])
      );

    end else begin : gen_cluster_sync

      pulp_cluster_sync i_cluster (
        .clk_i,
        .rst_ni (ndmreset_n),
        .ref_clk_i    (clk_i),
        .test_mode_i  (dft_glb_gt_se),
        .cluster_id_i (cluster_id),
        .fetch_en_i   (cl_fetch_en_i[i]),
        .eoc_o        (cl_eoc_o[i]),
        .busy_o       (cl_busy_o[i]),
        .dbg_irq_i    (core_debug_req[(i << 5) +: N_CORES]),
        .mailbox_evt_i,
        .ext_evt_1_i,
        .ext_evt_2_i,
        .ext_evt_3_i,
        .mem_ctrl,
        .dft_ram_gt_se,
        .dft_ram_bypass,
        .dft_ram_bp_clk_en,
        .slv          (cl_inp_dwced[i]),
        .mst          (cl_oup_prefilter[i])
      );
    end

    if (!pulp_pkg::CL_OUP_NO_ATOP) begin : gen_axi_atop_filter_cl_oup
      axi_atop_filter_intf #(
        .AXI_ID_WIDTH       (pulp_pkg::AXI_IW_CL_OUP),
        .AXI_ADDR_WIDTH     (pulp_pkg::AXI_AW),
        .AXI_DATA_WIDTH     (pulp_pkg::AXI_DW_CL),
        .AXI_USER_WIDTH     (pulp_pkg::AXI_UW),
        .AXI_MAX_WRITE_TXNS (pulp_cluster_cfg_pkg::DMA_MAX_N_TXNS)
      ) i_atop_filter_cl_oup (
        .clk_i,
        .rst_ni (ndmreset_n),
        .slv  (cl_oup_prefilter[i]),
        .mst  (cl_oup_predwc[i])
      );
    end else begin : gen_no_axi_atop_filter_cl_oup
      `AXI_ASSIGN(cl_oup_predwc[i], cl_oup_prefilter[i])
    end

    if (pulp_pkg::AXI_DW_CL != pulp_pkg::AXI_DW) begin : gen_dwc_cl_oup
      axi_dw_converter_intf #(
        .AXI_ADDR_WIDTH           (pulp_pkg::AXI_AW),
        .AXI_SLV_PORT_DATA_WIDTH  (pulp_pkg::AXI_DW_CL),
        .AXI_MST_PORT_DATA_WIDTH  (pulp_pkg::AXI_DW),
        .AXI_ID_WIDTH             (pulp_pkg::AXI_IW_CL_OUP),
        .AXI_USER_WIDTH           (pulp_pkg::AXI_UW),
        .AXI_MAX_READS            (8)
      ) i_dwc_cl_oup (
        .clk_i,
        .rst_ni (ndmreset_n),
        .slv    (cl_oup_predwc[i]),
        .mst    (cl_oup_prebuf[i])
      );

      axi_read_burst_buffer_wrap #(
        .ADDR_WIDTH   (pulp_pkg::AXI_AW),
        .DATA_WIDTH   (pulp_pkg::AXI_DW),
        .ID_WIDTH     (pulp_pkg::AXI_IW_CL_OUP),
        .USER_WIDTH   (pulp_pkg::AXI_UW),
        .BUF_DEPTH    (pulp_cluster_cfg_pkg::DMA_MAX_BURST_LEN)
      ) i_r_buf_cl_oup (
        .clk_i,
        .rst_ni (ndmreset_n),
        .slv    (cl_oup_prebuf[i]),
        .mst    (cl_oup[i])
      );
    end else begin : gen_no_dwc_cl_oup
      `AXI_ASSIGN(cl_oup[i], cl_oup_predwc[i]);
    end
  end

  soc_bus #(
    .AXI_AW               (pulp_pkg::AXI_AW),
    .AXI_DW               (pulp_pkg::AXI_DW),
    .AXI_UW               (pulp_pkg::AXI_UW),
    .AXI_IW_INP           (pulp_pkg::AXI_IW_SB_INP),
    .N_CLUSTERS           (N_CLUSTERS),
    .L2_N_PORTS           (L2_N_AXI_PORTS),
    .L2_N_BYTES_PER_PORT  (pulp_pkg::L2_SIZE/L2_N_AXI_PORTS),
    .DEBUG_N_BYTES        (pulp_cluster_cfg_pkg::DM_SIZE),
    .DEBUG_BASE_ADDR      (64'(pulp_cluster_cfg_pkg::DM_BASE_ADDR))
  ) i_soc_bus (
    .clk_i,
    .rst_ni     (ndmreset_n),
    .cl_slv     (cl_oup),
    .cl_mst     (cl_inp),
    .l2_mst     (l2_mst),
    .ext_mst    (ext_mst),
    .ext_slv    (ext_slv_remapped),
    .debug_slv  (debug_mst_dwced),
    .debug_mst  (debug_slv_predwc)
  );

  for (genvar i = 0; i < L2_N_AXI_PORTS; i++) begin: gen_l2_ports
    l2_mem #(
      .AXI_AW     (pulp_pkg::AXI_AW),
      .AXI_DW     (pulp_pkg::AXI_DW),
      .AXI_UW     (pulp_pkg::AXI_UW),
      .AXI_IW     (AXI_IW_SB_OUP),
      .N_BYTES    (pulp_pkg::L2_SIZE/L2_N_AXI_PORTS)
    ) i_l2_mem (
      .clk_i,
      .rst_ni (ndmreset_n),
      .slv    (l2_mst[i]),
      .mem_ctrl,
      .dft_ram_gt_se,
      .dft_ram_bypass,
      .dft_ram_bp_clk_en
    );
  end

  axi_id_resize #(
    .ADDR_WIDTH   (pulp_pkg::AXI_AW),
    .DATA_WIDTH   (pulp_pkg::AXI_DW),
    .USER_WIDTH   (pulp_pkg::AXI_UW),
    .ID_WIDTH_IN  (pulp_pkg::AXI_IW_SLV),
    .ID_WIDTH_OUT (pulp_pkg::AXI_IW_SB_INP),
    .TABLE_SIZE   (4)
  ) i_id_resize_ext_slv (
    .clk_i,
    .rst_ni (ndmreset_n),
    .in     (ext_slv),
    .out    (ext_slv_remapped)
  );

  axi_dw_converter_intf #(
    .AXI_ADDR_WIDTH           (pulp_pkg::AXI_AW),
    .AXI_SLV_PORT_DATA_WIDTH  (AXI_DW_DM),
    .AXI_MST_PORT_DATA_WIDTH  (pulp_pkg::AXI_DW),
    .AXI_ID_WIDTH             (pulp_pkg::AXI_IW_SB_INP),
    .AXI_USER_WIDTH           (pulp_pkg::AXI_UW),
    .AXI_MAX_READS            (1)
  ) i_dwc_debug_mst (
    .clk_i,
    .rst_ni (ndmreset_n),
    .slv    (debug_mst_predwc),
    .mst    (debug_mst_dwced)
  );

  axi_dw_converter_intf #(
    .AXI_ADDR_WIDTH           (pulp_pkg::AXI_AW),
    .AXI_SLV_PORT_DATA_WIDTH  (pulp_pkg::AXI_DW),
    .AXI_MST_PORT_DATA_WIDTH  (AXI_DW_DM),
    .AXI_ID_WIDTH             (AXI_IW_SB_OUP),
    .AXI_USER_WIDTH           (pulp_pkg::AXI_UW),
    .AXI_MAX_READS            (1)
  ) i_dwc_debug_slv (
    .clk_i,
    .rst_ni (ndmreset_n),
    .slv    (debug_slv_predwc),
    .mst    (debug_slv_dwced)
  );

  debug_system #(
    .AXI_AW (pulp_pkg::AXI_AW),
    .AXI_DW (AXI_DW_DM),
    .AXI_IW (pulp_pkg::AXI_IW_SB_INP),
    .AXI_UW (pulp_pkg::AXI_UW),
    .JTAG_IDCODE (pulp_pkg::JTAG_IDCODE),
    .N_CORES (pulp_cluster_cfg_pkg::N_CORES),
    .N_CLUSTERS (N_CLUSTERS),
    .MAX_HARTS (DM_MAX_HARTS)
  ) i_debug_system (
    .clk_i,
    .rst_ni,
    .test_en_i        (dft_mode),
    .ndmreset_no      (ndmreset_n),
    .jtag_tck_i,
    .jtag_trst_ni,
    .jtag_tdi_i,
    .jtag_tms_i,
    .jtag_tdo_o,
    .jtag_tdo_en_o,
    .core_debug_req_o (core_debug_req),
    .dm_slave         (debug_slv_dwced),
    .dm_master        (debug_mst_predwc)
  );

endmodule
