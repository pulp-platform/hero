// Copyright 2019 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

`include "axi/typedef.svh"

module hero_tb #(
  // TB Parameters
  parameter time          CLK_PERIOD = 1000ps,
  // SoC Parameters
  parameter int unsigned  N_CLUSTERS = 4,
  parameter int unsigned  AXI_DW = 256,
  parameter int unsigned  L2_N_AXI_PORTS = 1
);

  timeunit 1ps;
  timeprecision 1ps;

  localparam int unsigned AXI_IW = hero_pkg::axi_iw_sb_oup(N_CLUSTERS);
  typedef hero_pkg::addr_t      axi_addr_t;
  typedef logic [AXI_DW-1:0]    axi_data_t;
  typedef logic [AXI_IW-1:0]    axi_id_t;
  typedef logic [AXI_DW/8-1:0]  axi_strb_t;
  typedef hero_pkg::user_t      axi_user_t;
  `AXI_TYPEDEF_AW_CHAN_T(       axi_aw_t,     axi_addr_t, axi_id_t, axi_user_t);
  `AXI_TYPEDEF_W_CHAN_T(        axi_w_t,      axi_data_t, axi_strb_t, axi_user_t);
  `AXI_TYPEDEF_B_CHAN_T(        axi_b_t,      axi_id_t, axi_user_t);
  `AXI_TYPEDEF_AR_CHAN_T(       axi_ar_t,     axi_addr_t, axi_id_t, axi_user_t);
  `AXI_TYPEDEF_R_CHAN_T(        axi_r_t,      axi_data_t, axi_id_t, axi_user_t);
  `AXI_TYPEDEF_REQ_T(           axi_req_t,    axi_aw_t, axi_w_t, axi_ar_t);
  `AXI_TYPEDEF_RESP_T(          axi_resp_t,   axi_b_t, axi_r_t);

  typedef hero_pkg::lite_addr_t axi_lite_addr_t;
  typedef hero_pkg::lite_data_t axi_lite_data_t;
  typedef hero_pkg::lite_strb_t axi_lite_strb_t;
  `AXI_LITE_TYPEDEF_AX_CHAN_T(  axi_lite_ax_t,    axi_lite_addr_t, axi_id_t, axi_user_t);
  `AXI_LITE_TYPEDEF_W_CHAN_T(   axi_lite_w_t,     axi_lite_data_t, axi_lite_strb_t, axi_user_t);
  `AXI_LITE_TYPEDEF_B_CHAN_T(   axi_lite_b_t,     axi_id_t, axi_user_t);
  `AXI_LITE_TYPEDEF_R_CHAN_T(   axi_lite_r_t,     axi_lite_data_t, axi_id_t, axi_user_t);
  `AXI_LITE_TYPEDEF_REQ_T(      axi_lite_req_t,   axi_lite_ax_t, axi_lite_w_t);
  `AXI_LITE_TYPEDEF_RESP_T(     axi_lite_resp_t,  axi_lite_b_t, axi_lite_r_t);

  logic clk,
        rst_n;

  logic [N_CLUSTERS-1:0]  cl_busy,
                          cl_eoc,
                          cl_fetch_en;

  axi_req_t   dram_req;
  axi_resp_t  dram_resp;

  axi_lite_req_t  rab_conf_req;
  axi_lite_resp_t rab_conf_resp;

  clk_rst_gen #(
    .CLK_PERIOD     (CLK_PERIOD),
    .RST_CLK_CYCLES (10)
  ) i_clk_gen (
    .clk_o  (clk),
    .rst_no (rst_n)
  );

  hero #(
    .N_CLUSTERS     (N_CLUSTERS),
    .AXI_DW         (AXI_DW),
    .L2_N_AXI_PORTS (L2_N_AXI_PORTS),
    .axi_req_t      (axi_req_t),
    .axi_resp_t     (axi_resp_t),
    .axi_lite_req_t (axi_lite_req_t),
    .axi_lite_resp_t(axi_lite_resp_t)
  ) dut (
    .clk_i          (clk),
    .rst_ni         (rst_n),

    .cl_fetch_en_i  (cl_fetch_en),
    .cl_eoc_o       (cl_eoc),
    .cl_busy_o      (cl_busy),

    .dram_req_o     (dram_req),
    .dram_resp_i    (dram_resp),
    .rab_conf_req_i (rab_conf_req),
    .rab_conf_resp_o(rab_conf_resp)
  );

  // No memory attached at the moment.
  assign dram_resp = '0;

  // Simulation control
  initial begin
    cl_fetch_en = '0;
    rab_conf_req = '{default: '0};
    // Wait for reset.
    wait (rst_n);
    @(posedge clk);
    // Start cluster 0.
    cl_fetch_en[0] = 1'b1;
    // Wait for EOC of cluster 0 before terminating the simulation.
    wait (cl_eoc[0]);
    #1us;
    $finish();
  end

  // Fill TCDM memory.
  for (genvar iCluster = 0; iCluster < N_CLUSTERS; iCluster++) begin: gen_fill_tcdm_cluster
    for (genvar iBank = 0; iBank < 16; iBank++) begin: gen_fill_tcdm_bank
      initial begin
        $readmemh($sformatf("../test/slm_files/l1_0_%01d.slm", iBank),
          dut.gen_clusters[iCluster].gen_cluster_sync.i_cluster.i_ooc.i_bound.gen_tcdm_banks[iBank].i_mem.mem);
      end
    end
  end

  // Fill L2 memory.
  localparam N_SER_CUTS = dut.gen_l2_ports[0].i_l2_mem.N_SER_CUTS; // both same on all ports
  localparam N_PAR_CUTS = dut.gen_l2_ports[0].i_l2_mem.N_PAR_CUTS;
  for (genvar iPort = 0; iPort < L2_N_AXI_PORTS; iPort++) begin: gen_fill_l2_ports
    for (genvar iRow = 0; iRow < N_SER_CUTS; iRow++) begin: gen_fill_l2_rows
      for (genvar iCol = 0; iCol < N_PAR_CUTS; iCol++) begin: gen_fill_l2_cols
        int unsigned file_ser_idx = iPort*N_SER_CUTS + iRow;
        initial begin
          $readmemh($sformatf("../test/slm_files/l2_%01d_%01d.slm", file_ser_idx, iCol),
            dut.gen_l2_ports[iPort].i_l2_mem.gen_rows[iRow].gen_cols[iCol].i_mem_cut.mem);
        end
      end
    end
  end

  // Observe SoC bus for errors.
  for (genvar iCluster = 0; iCluster < N_CLUSTERS; iCluster++) begin: gen_assert_cluster
    assert property (@(posedge dut.clk_i) dut.rst_ni && dut.cl_oup[iCluster].r_valid
        |-> !dut.cl_oup[iCluster].r_resp[1])
      else $warning("R resp error at cl_oup[%01d]", iCluster);

    assert property (@(posedge dut.clk_i) dut.rst_ni && dut.cl_oup[iCluster].b_valid
        |-> !dut.cl_oup[iCluster].b_resp[1])
      else $warning("B resp error at cl_oup[%01d]", iCluster);
  end

endmodule
