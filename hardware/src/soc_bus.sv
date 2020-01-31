// Copyright 2019 ETH Zurich and University of Bologna.
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.

package automatic soc_bus_pkg;
  function int unsigned n_slaves(input int unsigned n_clusters);
    return n_clusters + 1;
  endfunction

  function int unsigned oup_id_w(input int unsigned n_clusters, inp_id_w);
    return inp_id_w + cf_math_pkg::log2(n_slaves(n_clusters));
  endfunction
endpackage

`include "axi/assign.svh"

module soc_bus #(
  parameter int unsigned  AXI_AW = 0,               // [bit]
  parameter int unsigned  AXI_DW = 0,               // [bit]
  parameter int unsigned  AXI_UW = 0,               // [bit]
  parameter int unsigned  AXI_IW_INP = 0,           // [bit]
  parameter int unsigned  N_CLUSTERS = 0,
  parameter int unsigned  L2_N_PORTS = 1,
  parameter int unsigned  L2_N_BYTES_PER_PORT = 0,  // [B]
  parameter int unsigned  PERIPH_N_BYTES = 0,       // [B]
  parameter int unsigned  MST_SLICE_DEPTH = 0,
  parameter int unsigned  SLV_SLICE_DEPTH = 0
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  AXI_BUS.Slave   cl_slv[N_CLUSTERS-1:0],
  AXI_BUS.Master  cl_mst[N_CLUSTERS-1:0],
  AXI_BUS.Master  l2_mst[L2_N_PORTS-1:0],
  AXI_BUS.Master  ext_mst,
  AXI_BUS.Slave   ext_slv
);

  localparam int unsigned N_REGIONS = 3;
  localparam int unsigned N_MASTERS = N_CLUSTERS + L2_N_PORTS + 1;
  localparam int unsigned N_SLAVES = soc_bus_pkg::n_slaves(N_CLUSTERS);
  localparam int unsigned IDX_L2_MEM = N_CLUSTERS;
  localparam int unsigned IDX_EXT = IDX_L2_MEM + 1;

  typedef logic [AXI_AW-1:0] addr_t;

  addr_t  [N_REGIONS-1:0][N_MASTERS-1:0]  start_addr,
                                          end_addr;
  logic   [N_REGIONS-1:0][N_MASTERS-1:0]  valid_rule;

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_INP),
    .AXI_USER_WIDTH (AXI_UW)
  ) slaves [N_SLAVES-1:0]();
  for (genvar i = 0; i < N_CLUSTERS; i++) begin: gen_bind_cluster_slv
    `AXI_ASSIGN(slaves[i], cl_slv[i]);
  end
  `AXI_ASSIGN(slaves[N_CLUSTERS], ext_slv);

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (soc_bus_pkg::oup_id_w(N_CLUSTERS, AXI_IW_INP)),
    .AXI_USER_WIDTH (AXI_UW)
  ) masters [N_MASTERS-1:0]();
//  FIXING ISSUE IN SYNTHESIS
//  for (genvar i = 0; i < N_CLUSTERS; i++) begin: gen_bind_clusters
    `AXI_ASSIGN(cl_mst[0], masters[0]);
//  end
//  for (genvar i = 0; i < L2_N_PORTS; i++) begin: gen_bind_l2
    `AXI_ASSIGN(l2_mst[0], masters[1]);
//  end
  `AXI_ASSIGN(ext_mst, masters[2]);

  // Address Map
  always_comb begin
    start_addr  = '0;
    end_addr    = '0;
    valid_rule  = '0;

    // Everything below Cluster 0 to EXT
    start_addr[0][IDX_EXT]  = 64'h0000_0000_0000_0000;
    end_addr[0][IDX_EXT]    = 64'h0000_0000_0FFF_FFFF;
    valid_rule[0][IDX_EXT]  = 1'b1;

    // Clusters
    for (int i = 0; i < N_CLUSTERS; i++) begin
      start_addr[0][i]  = 64'h0000_0000_1000_0000 + i * 32'h0040_0000;
      end_addr[0][i]    = start_addr[0][i] + 32'h002F_FFFF;
      valid_rule[0][i]  = 1'b1;
    end

    // Everthing in `0x1A..` to EXT
    start_addr[1][IDX_EXT]  = 64'h0000_0000_1A00_0000;
    end_addr[1][IDX_EXT]    = 64'h0000_0000_1AFF_FFFF;
    valid_rule[1][IDX_EXT]  = 1'b1;

    // L2 Memory
    for (int i = 0; i < L2_N_PORTS; i++) begin
      automatic int unsigned idx = IDX_L2_MEM + i;
      start_addr[0][idx]  = 64'h0000_0000_1C00_0000 + i*L2_N_BYTES_PER_PORT;
      end_addr[0][idx]    = start_addr[0][idx] + L2_N_BYTES_PER_PORT - 1;
      valid_rule[0][idx]  = 1'b1;
    end

    // Everything above L2 Memory to EXT
    start_addr[2][IDX_EXT]  = end_addr[0][IDX_L2_MEM+L2_N_PORTS-1] + 1;
    end_addr[2][IDX_EXT]    = 64'hFFFF_FFFF_FFFF_FFFF;
    valid_rule[2][IDX_EXT]  = 1'b1;
  end

  axi_node_wrap_with_slices #(
    .NB_MASTER          (N_MASTERS),
    .NB_SLAVE           (N_SLAVES),
    .NB_REGION          (N_REGIONS),
    .AXI_ADDR_WIDTH     (AXI_AW),
    .AXI_DATA_WIDTH     (AXI_DW),
    .AXI_ID_WIDTH       (AXI_IW_INP),
    .AXI_USER_WIDTH     (AXI_UW),
    .MASTER_SLICE_DEPTH (MST_SLICE_DEPTH),
    .SLAVE_SLICE_DEPTH  (SLV_SLICE_DEPTH)
  ) i_axi_node_wrap (
    .clk          (clk_i),
    .rst_n        (rst_ni),
    .test_en_i    (1'b0),
    .slave        (slaves),
    .master       (masters),
    .start_addr_i (start_addr),
    .end_addr_i   (end_addr),
    .valid_rule_i (valid_rule)
  );

endmodule
