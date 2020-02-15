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
    return inp_id_w + $clog2(n_slaves(n_clusters));
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
  parameter int unsigned  DEBUG_N_BYTES = 0,        // [B]
  parameter logic [63:0]  DEBUG_BASE_ADDR = 0
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  AXI_BUS.Slave   cl_slv[N_CLUSTERS-1:0],
  AXI_BUS.Master  cl_mst[N_CLUSTERS-1:0],
  AXI_BUS.Master  l2_mst[L2_N_PORTS-1:0],
  AXI_BUS.Master  ext_mst,
  AXI_BUS.Slave   ext_slv,
  AXI_BUS.Slave   debug_slv,
  AXI_BUS.Master  debug_mst
);

  localparam int unsigned N_MASTERS = N_CLUSTERS + L2_N_PORTS + 2; // ext and debug
  localparam int unsigned N_SLAVES = soc_bus_pkg::n_slaves(N_CLUSTERS) + 2; // ext and debug
  localparam int unsigned IDX_L2_MEM = N_CLUSTERS;
  localparam int unsigned IDX_EXT = IDX_L2_MEM + 1;
  localparam int unsigned IDX_DEBUG_MST = IDX_EXT + 1;

  localparam int unsigned IDX_EXT_SLV = N_CLUSTERS;
  localparam int unsigned IDX_DEBUG_SLV = IDX_EXT_SLV + 1;


  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW_INP),
    .AXI_USER_WIDTH (AXI_UW)
  ) slaves [N_SLAVES-1:0]();
  for (genvar i = 0; i < N_CLUSTERS; i++) begin: gen_bind_cluster_slv
    `AXI_ASSIGN(slaves[i], cl_slv[i]);
  end
  `AXI_ASSIGN(slaves[IDX_EXT_SLV], ext_slv);
  `AXI_ASSIGN(slaves[IDX_DEBUG_SLV], debug_slv);

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (soc_bus_pkg::oup_id_w(N_SLAVES, AXI_IW_INP)),
    .AXI_USER_WIDTH (AXI_UW)
  ) masters [N_MASTERS-1:0]();
//  TODO: FIXING ISSUE IN SYNTHESIS
//  for (genvar i = 0; i < N_CLUSTERS; i++) begin: gen_bind_clusters
    `AXI_ASSIGN(cl_mst[0], masters[0]);
//  end
//  for (genvar i = 0; i < L2_N_PORTS; i++) begin: gen_bind_l2
    `AXI_ASSIGN(l2_mst[0], masters[1]);
//  end
  `AXI_ASSIGN(ext_mst, masters[2]);
  //`AXI_ASSIGN(debug_mst, masters[IDX_DEBUG_MST]);
  `AXI_ASSIGN(debug_mst, masters[3]);

  // Address Map
  localparam int unsigned N_RULES = N_CLUSTERS + L2_N_PORTS + 1; // plus debug
  axi_pkg::xbar_rule_32_t [N_RULES-1:0] addr_map;
  // Clusters
  for (genvar i = 0; i < N_CLUSTERS; i++) begin : gen_addr_map_clusters
    logic [AXI_AW-1:0] cluster_base_addr = 32'h1000_0000 + i * 32'h0040_0000;
    assign addr_map[i] = '{
      idx:        i,
      start_addr: cluster_base_addr,
      end_addr:   cluster_base_addr + 32'h0030_0000
    };
  end
  for (genvar i = 0; i < L2_N_PORTS; i++) begin : gen_addr_map_l2
    logic [AXI_AW-1:0] l2_port_base_addr = 32'h1C00_0000 + i*L2_N_BYTES_PER_PORT;
    assign addr_map[N_CLUSTERS + i] = '{
      idx:        IDX_L2_MEM + i,
      start_addr: l2_port_base_addr,
      end_addr:   l2_port_base_addr + L2_N_BYTES_PER_PORT
    };
  end
  assign addr_map[N_CLUSTERS + L2_N_PORTS] = '{
    idx:        IDX_DEBUG_MST,
    start_addr: DEBUG_BASE_ADDR,
    end_addr:   DEBUG_BASE_ADDR + DEBUG_N_BYTES
  };
  // pragma translate_off
  `ifndef VERILATOR
    initial begin
      assert (AXI_AW == 32)
        else $fatal("Address map is only defined for 32-bit addresses!");
    end
  `endif
  // pragma translate_on

  localparam int unsigned MAX_TXNS_PER_CLUSTER =  pulp_cluster_cfg_pkg::N_CORES +
                                                  pulp_cluster_cfg_pkg::DMA_MAX_N_TXNS;

  localparam axi_pkg::xbar_cfg_t xbar_cfg = '{
    NoSlvPorts:         N_SLAVES,
    NoMstPorts:         N_MASTERS,
    MaxMstTrans:        MAX_TXNS_PER_CLUSTER,
    MaxSlvTrans:        N_CLUSTERS * MAX_TXNS_PER_CLUSTER,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_PORTS,
    AxiIdWidthSlvPorts: AXI_IW_INP,
    AxiIdUsedSlvPorts:  AXI_IW_INP,
    AxiAddrWidth:       AXI_AW,
    AxiDataWidth:       AXI_DW,
    NoAddrRules:        N_RULES
  };
  logic [$clog2(N_MASTERS)-1:0] default_mst_port;
  assign default_mst_port = IDX_EXT; // use external port as default master port
  axi_xbar_intf #(
    .AXI_USER_WIDTH (AXI_UW),
    .Cfg            (xbar_cfg),
    .rule_t         (axi_pkg::xbar_rule_32_t)
  ) i_axi_xbar (
    .clk_i,
    .rst_ni,
    .test_i                 (1'b0),
    .slv_ports              (slaves),
    .mst_ports              (masters),
    .addr_map_i             (addr_map),
    .en_default_mst_port_i  ({N_SLAVES{1'b1}}), // enable default master port for all slave ports
    .default_mst_port_i     ({N_SLAVES{default_mst_port}})
  );

endmodule
