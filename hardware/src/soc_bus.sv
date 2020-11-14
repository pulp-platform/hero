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
    return inp_id_w + cf_math_pkg::clog2(n_slaves(n_clusters));
  endfunction
endpackage

`include "axi/assign.svh"

module soc_bus #(
  parameter int unsigned  AXI_AW = 0,               // [bit]
  parameter int unsigned  AXI_DW = 0,               // [bit]
  parameter int unsigned  AXI_UW = 0,               // [bit]
  parameter int unsigned  AXI_IW_INP = 0,           // [bit]
  parameter int unsigned  N_CLUSTERS = 0,
  parameter int unsigned  L2_N_PORTS = 0,
  parameter int unsigned  L2_N_BYTES_PER_PORT = 0,  // [B]
  parameter int unsigned  PERIPH_N_BYTES = 0,       // [B]
  parameter int unsigned  MST_SLICE_DEPTH = 0,
  parameter int unsigned  SLV_SLICE_DEPTH = 0,
  // Dependent parameters, DO NOT OVERRIDE!
  parameter type addr_t = logic [AXI_AW-1:0]
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  AXI_BUS.Slave   cl_slv[N_CLUSTERS-1:0],
  AXI_BUS.Master  cl_mst[N_CLUSTERS-1:0],
  AXI_BUS.Master  l2_mst[L2_N_PORTS-1:0],
  AXI_BUS.Master  mbox_host_mst,
  output addr_t   mbox_host_base_addr_o,
  AXI_BUS.Master  mbox_pulp_mst,
  output addr_t   mbox_pulp_base_addr_o,
  AXI_BUS.Master  rab_mst,
  AXI_BUS.Slave   rab_slv
);

  localparam int unsigned N_REGIONS = 3;
  localparam int unsigned N_MASTERS = N_CLUSTERS + L2_N_PORTS + 3;
  localparam int unsigned N_SLAVES = soc_bus_pkg::n_slaves(N_CLUSTERS);
  localparam int unsigned IDX_L2_MEM = N_CLUSTERS;
  localparam int unsigned IDX_RAB = IDX_L2_MEM + 1;
  localparam int unsigned IDX_MBOX_HOST = IDX_RAB + 1;
  localparam int unsigned IDX_MBOX_PULP = IDX_MBOX_HOST + 1;

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
  `AXI_ASSIGN(slaves[N_CLUSTERS], rab_slv);

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (soc_bus_pkg::oup_id_w(N_CLUSTERS, AXI_IW_INP)),
    .AXI_USER_WIDTH (AXI_UW)
  ) masters [N_MASTERS-1:0]();
  for (genvar i = 0; i < N_CLUSTERS; i++) begin: gen_bind_clusters
    `AXI_ASSIGN(cl_mst[i], masters[i]);
  end
  for (genvar i = 0; i < L2_N_PORTS; i++) begin: gen_bind_l2
    `AXI_ASSIGN(l2_mst[i], masters[IDX_L2_MEM+i]);
  end
  `AXI_ASSIGN(rab_mst, masters[IDX_RAB]);
  `AXI_ASSIGN(mbox_host_mst, masters[IDX_MBOX_HOST]);
  `AXI_ASSIGN(mbox_pulp_mst, masters[IDX_MBOX_PULP]);

  // Address Map
  typedef axi_pkg::xbar_rule_64_t rule_t;
  localparam int unsigned NumRules = N_MASTERS + 2;
  rule_t [NumRules-1:0] addr_map;
  // Everything below Cluster 0 to RAB
  assign addr_map[0] = '{
    idx:        IDX_RAB,
    start_addr: 64'h0000_0000_0000_0000,
    end_addr:   64'h0000_0000_0FFF_FFFF
  };
  // Clusters
  for (genvar i = 0; i < N_CLUSTERS; i++) begin : gen_map_cluster
    assign addr_map[i+1] = '{
      idx:        i,
      start_addr: 64'h0000_0000_1000_0000 + i * 32'h0040_0000,
      end_addr:   64'h0000_0000_1000_0000 + i * 32'h0040_0000 + 32'h002F_FFFF
    };
  end
  // Everthing in `0x1A..` to RAB
  assign addr_map[1+N_CLUSTERS] = '{
    idx:        IDX_RAB,
    start_addr: 64'h0000_0000_1A00_0000,
    end_addr:   64'h0000_0000_1AFF_FFFF
  };
  // Mailbox for PULP and Host
  logic [15:0] mbox_len;
  assign mbox_len = 16'h1000; // length of address space of one mailbox slave (multiples of 4 KiB)
  assign mbox_pulp_base_addr_o = 64'h0000_0000_1B80_0000;
  assign addr_map[2+N_CLUSTERS] = '{
    idx:        IDX_MBOX_PULP,
    start_addr: mbox_pulp_base_addr_o,
    end_addr:   mbox_pulp_base_addr_o + mbox_len - 1
  };
  assign mbox_host_base_addr_o = mbox_pulp_base_addr_o + mbox_len;
  assign addr_map[3+N_CLUSTERS] = '{
    idx:        IDX_MBOX_HOST,
    start_addr: mbox_host_base_addr_o,
    end_addr:   mbox_host_base_addr_o + mbox_len - 1
  };
  // L2 Memory
  for (genvar i = 0; i < L2_N_PORTS; i++) begin : gen_map_l2_port
    assign addr_map[3+N_CLUSTERS+1+i] = '{
      idx:        IDX_L2_MEM + i,
      start_addr: 64'h0000_0000_1C00_0000 + i*L2_N_BYTES_PER_PORT,
      end_addr:   64'h0000_0000_1C00_0000 + (i+1)*L2_N_BYTES_PER_PORT - 1
    };
  end
  // Everything above L2 Memory to RAB
  assign addr_map[3+N_CLUSTERS+1+L2_N_PORTS] = '{
    idx:        IDX_RAB,
    start_addr: 64'h0000_0000_1C00_0000 + L2_N_PORTS*L2_N_BYTES_PER_PORT,
    end_addr:   64'hFFFF_FFFF_FFFF_FFFF
  };

  localparam axi_pkg::xbar_cfg_t XbarCfg = '{
    NoSlvPorts:         N_SLAVES,
    NoMstPorts:         N_MASTERS,
    MaxMstTrans:        4,
    MaxSlvTrans:        4,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_PORTS,
    AxiIdWidthSlvPorts: AXI_IW_INP,
    AxiIdUsedSlvPorts:  AXI_IW_INP,
    AxiAddrWidth:       AXI_AW,
    AxiDataWidth:       AXI_DW,
    NoAddrRules:        NumRules
  };
  axi_xbar_intf #(
    .AXI_USER_WIDTH (AXI_UW),
    .Cfg            (XbarCfg),
    .rule_t         (rule_t)
  ) i_axi_xbar (
    .clk_i,
    .rst_ni,
    .test_i                 (1'b0),
    .slv_ports              (slaves),
    .mst_ports              (masters),
    .addr_map_i             (addr_map),
    .en_default_mst_port_i  ('0),
    .default_mst_port_i     ('0)
  );

endmodule
