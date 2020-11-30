// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/*
 * dmac_wrap.sv
 * Thomas Benz <tbenz@iis.ee.ethz.ch>
 */
`include "axi/assign.svh"
`include "axi/typedef.svh"
module dmac_wrap
#(
  parameter NB_CORES           = 4,
  parameter NB_OUTSND_BURSTS   = 8,
  parameter MCHAN_BURST_LENGTH = 256,
  parameter AXI_ADDR_WIDTH     = 32,
  parameter AXI_DATA_WIDTH     = 64,
  parameter AXI_USER_WIDTH     = 6,
  parameter AXI_ID_WIDTH       = 4,
  parameter PE_ID_WIDTH        = 1,
  parameter TCDM_ADD_WIDTH     = 13,
  parameter DATA_WIDTH         = 32,
  parameter ADDR_WIDTH         = 32,
  parameter BE_WIDTH           = DATA_WIDTH/8
) (
  input logic                      clk_i,
  input logic                      rst_ni,
  input logic                      test_mode_i,
  XBAR_PERIPH_BUS.Slave            pe_ctrl_slave,
  XBAR_TCDM_BUS.Slave              ctrl_slave[NB_CORES-1:0],
  XBAR_TCDM_BUS.Master             tcdm_master[3:0],
  AXI_BUS.Master                   ext_master,
  output logic [NB_CORES-1:0]      term_event_o,
  output logic [NB_CORES-1:0]      term_irq_o,
  output logic                     term_event_pe_o,
  output logic                     term_irq_pe_o,
  output logic                     busy_o
);

  // CORE --> MCHAN CTRL INTERFACE BUS SIGNALS
  logic [NB_CORES-1:0][DATA_WIDTH-1:0] config_wdata;
  logic [NB_CORES-1:0][ADDR_WIDTH-1:0] config_add;
  logic [NB_CORES-1:0]                 config_req;
  logic [NB_CORES-1:0]                 config_wen;
  logic [NB_CORES-1:0][BE_WIDTH-1:0]   config_be;
  logic [NB_CORES-1:0]                 config_gnt;
  logic [NB_CORES-1:0][DATA_WIDTH-1:0] config_r_rdata;
  logic [NB_CORES-1:0]                 config_r_valid;

  // tie-off pe control ports
  for (genvar i = 0; i < NB_CORES; i++) begin : gen_ctrl_registers
    assign config_add[i]         = ctrl_slave[i].add;
    assign config_req[i]         = ctrl_slave[i].req;
    assign config_wdata[i]       = ctrl_slave[i].wdata;
    assign config_wen[i]         = ctrl_slave[i].wen;
    assign config_be[i]          = ctrl_slave[i].be;
    assign ctrl_slave[i].gnt     = config_gnt[i];
    assign ctrl_slave[i].r_opc   = '0;
    assign ctrl_slave[i].r_valid = config_r_rdata[i];
    assign ctrl_slave[i].r_rdata = config_r_valid[i];
  end

  // tie-off TCDM master port
  for (genvar i = 0; i < 4; i++) begin : gen_tcdm_master
      assign tcdm_master[i].add   = '0;
      assign tcdm_master[i].req   = '0;
      assign tcdm_master[i].wdata = '0;
      assign tcdm_master[i].wen   = '0;
      assign tcdm_master[i].be    = '0;
  end

  // AXI4+ATOP types
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_ID_WIDTH-1:0]       id_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  // AXI4+ATOP channels typedefs
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)
  // BUS definitions
  req_t  dma_req;
  resp_t dma_rsp;
  // interface to structs
  `AXI_ASSIGN_FROM_REQ(ext_master, dma_req)
  `AXI_ASSIGN_TO_RESP(dma_rsp, ext_master)

  pulp_cluster_dma_frontend #(
    .NumCores          ( NB_CORES        ),
    .PerifIdWidth      ( PE_ID_WIDTH     ),
    .DmaAxiIdWidth     ( AXI_ID_WIDTH    ),
    .DmaDataWidth      ( AXI_DATA_WIDTH  ),
    .DmaAddrWidth      ( AXI_ADDR_WIDTH  ),
    .AxiAxReqDepth     ( 0               ),
    .TfReqFifoDepth    ( 0               ),
    .axi_req_t         ( req_t           ),
    .axi_res_t         ( resp_t          )
  ) i_pulp_cluster_dma_frontend (
    .clk_i                   ( clk_i                   ),
    .rst_ni                  ( rst_ni                  ),
    .cluster_id_i            ( '0                      ),
    .ctrl_pe_targ_req_i      ( pe_ctrl_slave.req       ),
    .ctrl_pe_targ_type_i     ( pe_ctrl_slave.wen       ),
    .ctrl_pe_targ_be_i       ( pe_ctrl_slave.be        ),
    .ctrl_pe_targ_add_i      ( pe_ctrl_slave.add       ),
    .ctrl_pe_targ_data_i     ( pe_ctrl_slave.wdata     ),
    .ctrl_pe_targ_id_i       ( pe_ctrl_slave.id        ),
    .ctrl_pe_targ_gnt_o      ( pe_ctrl_slave.gnt       ),
    .ctrl_pe_targ_r_valid_o  ( pe_ctrl_slave.r_valid   ),
    .ctrl_pe_targ_r_data_o   ( pe_ctrl_slave.r_rdata   ),
    .ctrl_pe_targ_r_opc_o    ( pe_ctrl_slave.r_opc     ),
    .ctrl_pe_targ_r_id_o     ( pe_ctrl_slave.r_id      ),
    .ctrl_targ_req_i         ( config_req              ),
    .ctrl_targ_type_i        ( config_wen              ),
    .ctrl_targ_be_i          ( config_be               ),
    .ctrl_targ_add_i         ( config_add              ),
    .ctrl_targ_data_i        ( config_wdata            ),
    .ctrl_targ_gnt_o         ( config_gnt              ),
    .ctrl_targ_r_valid_o     ( config_r_valid          ),
    .ctrl_targ_r_data_o      ( config_r_rdata          ),
    .axi_dma_req_o           ( dma_req                 ),
    .axi_dma_res_i           ( dma_rsp                 ),
    .busy_o                  ( busy_o                  ),
    .term_event_o            ( term_event_o            ),
    .term_irq_o              ( term_irq_o              ),
    .term_event_pe_o         ( term_event_pe_o         ),
    .term_irq_pe_o           ( term_irq_pe_o           )
  );

endmodule : dmac_wrap
