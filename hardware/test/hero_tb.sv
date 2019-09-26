// Copyright 2019 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

`include "axi/typedef.svh"

`define wait_for(signal) \
  do \
    @(posedge clk); \
  while (!signal);

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
  localparam int unsigned AXI_SW = AXI_DW/8;  // width of strobe
  typedef hero_pkg::addr_t      axi_addr_t;
  typedef logic [AXI_DW-1:0]    axi_data_t;
  typedef logic [AXI_IW-1:0]    axi_id_t;
  typedef logic [AXI_SW-1:0]    axi_strb_t;
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

  // Emulate infinite memory with AXI slave port.
  initial begin
    automatic logic [7:0] mem[axi_addr_t];
    automatic axi_ar_t ar_queue[$];
    automatic axi_aw_t aw_queue[$];
    automatic axi_b_t b_queue[$];
    automatic shortint unsigned r_cnt = 0, w_cnt = 0;
    dram_resp = '0;
    wait (rst_n);
    @(posedge clk);
    fork
      // AW
      forever begin
        dram_resp.aw_ready = 1'b1;
        if (dram_req.aw_valid) begin
          aw_queue.push_back(dram_req.aw);
        end
        @(posedge clk);
      end
      // W
      forever begin
        if (aw_queue.size() != 0) begin
          dram_resp.w_ready = 1'b1;
          if (dram_req.w_valid) begin
            automatic axi_addr_t addr = aw_queue[0].addr;
            automatic axi_pkg::size_t size = aw_queue[0].size;
            for (shortint unsigned
                i_byte = axi_pkg::beat_lower_byte(addr, size, AXI_SW, w_cnt);
                i_byte <= axi_pkg::beat_upper_byte(addr, size, AXI_SW, w_cnt);
                i_byte++) begin
              if (dram_req.w.strb[i_byte]) begin
                automatic axi_addr_t byte_addr = (addr / AXI_SW) * AXI_SW + i_byte;
                mem[byte_addr] = dram_req.w.data[i_byte*8+:8];
              end
            end
            if (w_cnt == aw_queue[0].len) begin
              automatic axi_b_t b_beat = '0;
              assert (dram_req.w.last) else $error("Expected last beat of W burst!");
              b_beat.id = aw_queue[0].id;
              b_beat.resp = axi_pkg::RESP_OKAY;
              b_queue.push_back(b_beat);
              w_cnt = 0;
              void'(aw_queue.pop_front());
            end else begin
              assert (!dram_req.w.last) else $error("Did not expect last beat of W burst!");
              w_cnt++;
            end
          end
        end else begin
          dram_resp.w_ready = 1'b0;
        end
        @(posedge clk);
      end
      // B
      forever begin
        if (b_queue.size() != 0) begin
          dram_resp.b = b_queue[0];
          dram_resp.b_valid = 1'b1;
          if (dram_req.b_ready) begin
            void'(b_queue.pop_front());
          end
        end else begin
          dram_resp.b_valid = 1'b0;
        end
        @(posedge clk);
      end
      // AR
      forever begin
        dram_resp.ar_ready = 1'b1;
        if (dram_req.ar_valid) begin
          ar_queue.push_back(dram_req.ar);
        end
        @(posedge clk);
      end
      // R
      forever begin
        if (ar_queue.size() != 0) begin
          automatic axi_addr_t addr = ar_queue[0].addr;
          automatic axi_pkg::size_t size = ar_queue[0].size;
          automatic axi_r_t r_beat = '0;
          r_beat.data = 'x;
          r_beat.id = ar_queue[0].id;
          r_beat.resp = axi_pkg::RESP_OKAY;
          for (shortint unsigned
              i_byte = axi_pkg::beat_lower_byte(addr, size, AXI_SW, r_cnt);
              i_byte <= axi_pkg::beat_upper_byte(addr, size, AXI_SW, r_cnt);
              i_byte++) begin
            automatic axi_addr_t byte_addr = (addr / AXI_SW) * AXI_SW + i_byte;
            r_beat.data[i_byte*8+:8] = mem[byte_addr];
          end
          if (r_cnt == ar_queue[0].len) begin
            r_beat.last = 1'b1;
          end
          dram_resp.r = r_beat;
          dram_resp.r_valid = 1'b1;
          if (dram_req.r_ready) begin
            if (r_beat.last) begin
              r_cnt = 0;
              void'(ar_queue.pop_front());
            end else begin
              r_cnt++;
            end
          end
        end else begin
          dram_resp.r_valid = 1'b0;
        end
        @(posedge clk);
      end
    join
  end

  task write_rab(input axi_lite_addr_t addr, input axi_lite_data_t data);
    rab_conf_req.aw.addr = addr;
    rab_conf_req.aw.size = 3'h3;
    rab_conf_req.aw_valid = 1'b1;
    `wait_for(rab_conf_resp.aw_ready)
    rab_conf_req.aw_valid = 1'b0;
    rab_conf_req.w.data = data;
    rab_conf_req.w.strb = '1;
    rab_conf_req.w_valid = 1'b1;
    `wait_for(rab_conf_resp.w_ready)
    rab_conf_req.w_valid = 1'b0;
    rab_conf_req.b_ready = 1'b1;
    `wait_for(rab_conf_resp.b_valid)
    rab_conf_req.b_ready = 1'b0;
  endtask

  task write_rab_slice(input axi_lite_addr_t slice_addr, input axi_addr_t first,
      input axi_addr_t last, input axi_addr_t phys_addr);
    write_rab(slice_addr+8'h00, first);
    write_rab(slice_addr+8'h08, last);
    write_rab(slice_addr+8'h10, phys_addr);
    write_rab(slice_addr+8'h18, 64'h7);
  endtask

  // Simulation control
  initial begin
    cl_fetch_en = '0;
    rab_conf_req = '{default: '0};
    // Wait for reset.
    wait (rst_n);
    @(posedge clk);

    // Set up RAB slice from PULP to external memory: everything below 0x1000_0000 (except zero
    // page).
    write_rab_slice(32'hA0, 64'h0000_0000_0000_1000, 64'h0000_0000_0FFF_FFFF,
        64'h0000_0000_0000_1000);
    // Set up RAB slice from PULP to external memory: everything above 0x1D00_0000.
    write_rab_slice(32'hC0, 64'h0000_0000_1D00_0000, 64'hFFFF_FFFF_FFFF_FFFF,
        64'h0000_0000_1D00_0000);

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
