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

module soc_peripherals #(
  parameter int unsigned  AXI_AW      = 0,
  parameter int unsigned  AXI_IW      = 0,
  parameter int unsigned  AXI_UW      = 0,
  parameter int unsigned  AXI_DW      = 0,
  parameter int unsigned  N_CORES     = 0,
  parameter int unsigned  N_CLUSTERS  = 0
) (
  input  logic  clk_i,
  input  logic  rst_ni,

  input  logic  test_en_i,

  AXI_BUS.Slave axi
);

  localparam int unsigned N_SLAVES = 2;

  localparam int unsigned SOC_CTRL_START = pulp_cluster_cfg_pkg::SOC_PERIPH_BASE_ADDR + 16'h3000;
  localparam int unsigned SOC_CTRL_END   = SOC_CTRL_START + 16'h0FFF;
  localparam int unsigned STD_OUT_START  = pulp_cluster_cfg_pkg::SOC_PERIPH_BASE_ADDR + 16'h4000;
  localparam int unsigned STD_OUT_END    = STD_OUT_START  + 16'h0FFF;

  // AXI to AXI Lite
  AXI_LITE #(
    .AXI_ADDR_WIDTH(AXI_AW),
    .AXI_DATA_WIDTH(AXI_DW)
  ) axi_lite ();

  axi_to_axi_lite_intf #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW),
    .AXI_USER_WIDTH (AXI_UW)
  ) i_axi_to_axi_lite (
    .clk_i,
    .rst_ni,
    .testmode_i (test_en_i),
    .slv        (axi      ),
    .mst        (axi_lite )
  );

  // AXI LITE to APB

  // Address mapping
  typedef struct packed {
    int unsigned       idx;
    logic [AXI_AW-1:0] start_addr;
    logic [AXI_AW-1:0] end_addr;
  } rule_t;
  rule_t [1:0]   addr_map;
  assign addr_map[0] = '{idx: 0, start_addr: SOC_CTRL_START, end_addr: SOC_CTRL_END};
  assign addr_map[1] = '{idx: 1, start_addr: STD_OUT_START,  end_addr: STD_OUT_END };

  logic [AXI_AW-1:0]               paddr;
  logic [2:0]                      pprot;
  logic [N_SLAVES-1:0]             psel;
  logic                            penable;
  logic                            pwrite;
  logic [AXI_DW-1:0]               pwdata;
  logic [AXI_DW/8-1:0]             pstrb;
  logic [N_SLAVES-1:0]             pready;
  logic [N_SLAVES-1:0][AXI_DW-1:0] prdata;
  logic [N_SLAVES-1:0]             pslverr;

  axi_lite_to_apb_intf #(
    .NoApbSlaves (N_SLAVES),
    .NoRules     (N_SLAVES),
    .AddrWidth   (AXI_AW  ),
    .DataWidth   (AXI_DW  ),
    .rule_t      (rule_t  )
  ) i_axi_lite_to_apb (
    .clk_i,
    .rst_ni,
    .slv        (axi_lite    ),
    .paddr_o    (paddr       ),
    .pprot_o    (pprot       ),
    .pselx_o    (psel        ),
    .penable_o  (penable     ),
    .pwrite_o   (pwrite      ),
    .pwdata_o   (pwdata      ),
    .pstrb_o    (pstrb       ),
    .pready_i   (pready      ),
    .prdata_i   (prdata      ),
    .pslverr_i  (pslverr     ),
    .addr_map_i (addr_map    )
  );

  APB_BUS #(
    .APB_ADDR_WIDTH (AXI_AW),
    .APB_DATA_WIDTH (AXI_DW)
  ) apb_periphs[N_SLAVES-1:0] ();

  for (genvar slv = 0; slv < N_SLAVES; slv++) begin: gen_apb_assign
    assign apb_periphs[slv].paddr = paddr;
    assign apb_periphs[slv].pwdata = pwdata;
    assign apb_periphs[slv].pwrite = pwrite;
    assign apb_periphs[slv].psel = psel[slv];
    assign apb_periphs[slv].penable = penable;
    assign prdata[slv] = apb_periphs[slv].prdata;
    assign pready[slv] = apb_periphs[slv].pready;
    assign pslverr[slv] = apb_periphs[slv].pslverr;
  end

  // Peripherals
  soc_ctrl_regs #(
    .N_CORES    (N_CORES),
    .N_CLUSTERS (N_CLUSTERS),
    .ADDR_WIDTH (AXI_AW),
    .DATA_WIDTH (AXI_DW),
    .BASE_ADDR  (SOC_CTRL_START)
  ) i_soc_ctrl_regs (
    .clk_i,
    .rst_ni,
    .apb    (apb_periphs[0])
  );

  `ifndef TARGET_SYNTHESIS
    apb_stdout #(
      .N_CORES    (N_CORES),
      .N_CLUSTERS (N_CLUSTERS),
      .ADDR_WIDTH (AXI_AW),
      .DATA_WIDTH (AXI_DW)
    ) i_stdout (
      .clk_i,
      .rst_ni,
      .apb  (apb_periphs[1])
    );
  `else
    assign apb_periphs[1].pready = 1'b1;
    assign apb_periphs[1].pslverr = 1'b1;
    assign apb_periphs[1].prdata = '0;
  `endif

endmodule
