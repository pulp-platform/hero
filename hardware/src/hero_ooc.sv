import axi_pkg::*;
import hero_pkg::*;

module hero_ooc #(
  parameter int unsigned  AXI_DW = 256,         // [bit]
  parameter int unsigned  N_CLUSTERS = 4,
  localparam type data_t = logic [AXI_DW-1:0],
  localparam type id_mst_t = logic [axi_iw_sb_oup(N_CLUSTERS)-1:0],
  localparam type strb_t = logic [AXI_DW/8-1:0]
) (
  // Clocks and Resets
  input  logic                  clk_i,
  input  logic                  rst_ni,

  // Cluster Control
  input  logic [N_CLUSTERS-1:0] cl_fetch_en_i,
  output logic [N_CLUSTERS-1:0] cl_eoc_o,
  output logic [N_CLUSTERS-1:0] cl_busy_o
);

  hero #(
    .N_CLUSTERS (N_CLUSTERS),
    .AXI_DW     (AXI_DW)
  ) i_bound (
    .clk_i,
    .rst_ni,
    .cl_fetch_en_i,
    .cl_eoc_o,
    .cl_busy_o
  );

endmodule
