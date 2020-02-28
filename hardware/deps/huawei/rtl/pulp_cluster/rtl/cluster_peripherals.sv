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
 * cluster_peripherals.sv
 * Davide Rossi <davide.rossi@unibo.it>
 * Antonio Pullini <pullinia@iis.ee.ethz.ch>
 * Igor Loi <igor.loi@unibo.it>
 * Francesco Conti <fconti@iis.ee.ethz.ch>
 */

import pulp_cluster_package::*;

module cluster_peripherals
#(
  parameter NB_CORES       = 8,
  parameter NB_MPERIPHS    = 1,
  parameter NB_CACHE_BANKS = 4,
  parameter NB_SPERIPHS    = 8,
  parameter NB_TCDM_BANKS  = 8,
  parameter ROM_BOOT_ADDR  = 32'h1A000000,
  parameter BOOT_ADDR      = 32'h1C000000,
  parameter EVNT_WIDTH     = 8,
  parameter SP_ICACHE      = 1'b0,
  parameter MP_ICACHE      = 1'b0,
  parameter PRI_ICACHE     = 1'b0,
  parameter FEATURE_DEMUX_MAPPED = 1
)
(
  input  logic                        clk_i,
  input  logic                        rst_ni,
  input  logic                        ref_clk_i,
  input  logic                        test_mode_i,

  input  logic                        en_sa_boot_i,
  input  logic                        fetch_en_i,
  input  logic [NB_CORES-1:0]         core_busy_i,
  output logic [NB_CORES-1:0]         core_clk_en_o,
  output logic                        fregfile_disable_o,

  output logic [NB_CORES-1:0][31:0]   boot_addr_o,

  output logic                        cluster_cg_en_o,

  output logic                        busy_o,

  XBAR_PERIPH_BUS.Slave               speriph_slave[NB_SPERIPHS-1:0],
  XBAR_PERIPH_BUS.Slave               core_eu_direct_link[NB_CORES-1:0],

  XBAR_PERIPH_BUS.Master              dma_cfg_master,
  input logic                         dma_cl_event_i,
  input logic                         dma_cl_irq_i,

  output logic                        soc_periph_evt_ready_o,
  input  logic                        soc_periph_evt_valid_i,
  input  logic [EVNT_WIDTH-1:0]       soc_periph_evt_data_i,
  

  input  logic [NB_CORES-1:0]         dbg_core_halted_i,
  output logic [NB_CORES-1:0]         dbg_core_halt_o,
  output logic [NB_CORES-1:0]         dbg_core_resume_o,


  output logic                        eoc_o,
  output logic [NB_CORES-1:0]         fetch_enable_reg_o, //fetch enable driven by the internal register
  output logic [NB_CORES-1:0][4:0]    irq_id_o,
  input  logic [NB_CORES-1:0][4:0]    irq_ack_id_i,
  output logic [NB_CORES-1:0]         irq_req_o,
  input  logic [NB_CORES-1:0]         irq_ack_i,

  input  logic [NB_CORES-1:0]         dbg_req_i,
  output logic [NB_CORES-1:0]         dbg_req_o,

  input  logic                        mailbox_evt_i,

  // SRAM SPEED REGULATION --> TCDM
  output logic [1:0]                  TCDM_arb_policy_o,

  XBAR_PERIPH_BUS.Master              hwpe_cfg_master,
  input logic [NB_CORES-1:0][3:0]     hwpe_events_i,
  output logic                        hwpe_sel_o,
  output logic                        hwpe_en_o,

  // for private I$
  SP_ICACHE_CTRL_UNIT_BUS.Master      IC_ctrl_unit_bus_main[NB_CACHE_BANKS],
  PRI_ICACHE_CTRL_UNIT_BUS.Master     IC_ctrl_unit_bus_pri[NB_CORES],
  output logic                        special_core_icache_cfg_o,
  output logic [NB_CORES-1:0]         enable_l1_l15_prefetch_o,

  // for SP I$
  SP_ICACHE_CTRL_UNIT_BUS.Master      IC_ctrl_unit_bus_sp[NB_CACHE_BANKS],
  L0_CTRL_UNIT_BUS.Master             L0_ctrl_unit_bus_sp[NB_CORES],

  // for MP I$
  MP_PF_ICACHE_CTRL_UNIT_BUS.Master   IC_ctrl_unit_bus_mp
);
   
  logic                      s_timer_out_lo_event;
  logic                      s_timer_out_hi_event;
  logic                      s_timer_in_lo_event;
  logic                      s_timer_in_hi_event;
  
  logic [NB_CORES-1:0][31:0] s_cluster_events;
  logic [NB_CORES-1:0][3:0]  s_acc_events;
  logic [NB_CORES-1:0][1:0]  s_timer_events;
  logic [NB_CORES-1:0][1:0]  s_dma_events;
  

  logic [NB_CORES-1:0]  s_fetch_en_cc;

  logic [NB_SPERIPH_PLUGS_EU-1:0]             eu_speriph_plug_req;
  logic [NB_SPERIPH_PLUGS_EU-1:0][31:0]       eu_speriph_plug_add;
  logic [NB_SPERIPH_PLUGS_EU-1:0]             eu_speriph_plug_wen;
  logic [NB_SPERIPH_PLUGS_EU-1:0][31:0]       eu_speriph_plug_wdata;
  logic [NB_SPERIPH_PLUGS_EU-1:0][3:0]        eu_speriph_plug_be;
  logic [NB_SPERIPH_PLUGS_EU-1:0][NB_CORES:0] eu_speriph_plug_id;

  logic soc_periph_evt_valid, soc_periph_evt_ready;
  logic [7:0] soc_periph_evt_data;
   
  // internal speriph bus to combine multiple plugs to new event unit
  XBAR_PERIPH_BUS speriph_slave_eu_comb();
  
  // decide between common or core-specific event sources
  generate
    for (genvar I=0; I<NB_CORES; I++) begin
      assign s_cluster_events[I] = 32'd0;
      assign s_acc_events[I]     = hwpe_events_i[I];
      assign s_timer_events[I]   = {s_timer_out_hi_event,s_timer_out_lo_event};
      assign s_dma_events[I][0] = dma_cl_event_i;
      assign s_dma_events[I][1] = dma_cl_irq_i;

    end
  endgenerate
  
  assign fetch_enable_reg_o = s_fetch_en_cc;

  //********************************************************
   //************ END OF COMPUTATION UNIT *******************
   //********************************************************
  cluster_control_unit #(
    .PER_ID_WIDTH  ( NB_CORES+NB_MPERIPHS        ),
    .NB_CORES      ( NB_CORES                    ),
    .ROM_BOOT_ADDR ( ROM_BOOT_ADDR               ),
    .BOOT_ADDR     ( BOOT_ADDR                   )
  ) cluster_control_unit_i (
    .clk_i              ( clk_i                      ),
    .rst_ni             ( rst_ni                     ),
    .en_sa_boot_i       ( en_sa_boot_i               ),
    .fetch_en_i         ( fetch_en_i                 ),
    .cluster_cg_en_o    ( cluster_cg_en_o            ),
    .boot_addr_o        ( boot_addr_o                ),
    .speriph_slave      ( speriph_slave[SPER_EOC_ID] ),
    .eoc_o              ( eoc_o                      ),
    .event_o            (                            ),
    .hwpe_sel_o         ( hwpe_sel_o                 ),
    .hwpe_en_o          ( hwpe_en_o                  ),
    .core_halted_i      ( dbg_core_halted_i          ),
    .core_halt_o        ( dbg_core_halt_o            ),
    .core_resume_o      ( dbg_core_resume_o          ),
    .fetch_enable_o     ( s_fetch_en_cc              ),
    .TCDM_arb_policy_o  ( TCDM_arb_policy_o          ),
    .fregfile_disable_o ( fregfile_disable_o         )
  );

  //********************************************************
  //******************** TIMER *****************************
  //********************************************************
  
  cluster_timer_wrap #(
    .ID_WIDTH(NB_CORES+NB_MPERIPHS)
  ) cluster_timer_wrap_i (
    .clk_i        ( clk_i                        ),
    .rst_ni       ( rst_ni                       ),
    .ref_clk_i    ( ref_clk_i                    ),
    .periph_slave ( speriph_slave[SPER_TIMER_ID] ),
    .event_lo_i   ( 1'b0                         ),
    .event_hi_i   ( 1'b0                         ),
    .irq_lo_o     ( s_timer_out_lo_event         ),
    .irq_hi_o     ( s_timer_out_hi_event         ),
    .busy_o       ( busy_o                       )
  );
   
  //********************************************************
  //******************** NEW EVENT UNIT ********************
  //********************************************************

  // combine number of required slave ports for event unit
  generate
    for (genvar I = 0; I < NB_SPERIPH_PLUGS_EU; I++ ) begin
      assign speriph_slave[SPER_EVENT_U_ID+I].gnt     = speriph_slave_eu_comb.gnt;
      assign speriph_slave[SPER_EVENT_U_ID+I].r_valid = speriph_slave_eu_comb.r_valid;
      assign speriph_slave[SPER_EVENT_U_ID+I].r_opc   = speriph_slave_eu_comb.r_opc;
      assign speriph_slave[SPER_EVENT_U_ID+I].r_id    = speriph_slave_eu_comb.r_id;
      assign speriph_slave[SPER_EVENT_U_ID+I].r_rdata = speriph_slave_eu_comb.r_rdata;
      assign eu_speriph_plug_req[I]   = speriph_slave[SPER_EVENT_U_ID+I].req;
      assign eu_speriph_plug_add[I]   = speriph_slave[SPER_EVENT_U_ID+I].add;
      assign eu_speriph_plug_wen[I]   = speriph_slave[SPER_EVENT_U_ID+I].wen;
      assign eu_speriph_plug_wdata[I] = speriph_slave[SPER_EVENT_U_ID+I].wdata;
      assign eu_speriph_plug_be[I]    = speriph_slave[SPER_EVENT_U_ID+I].be;
      assign eu_speriph_plug_id[I]    = speriph_slave[SPER_EVENT_U_ID+I].id;
    end
  endgenerate

  assign speriph_slave_eu_comb.req   = |eu_speriph_plug_req;
  assign speriph_slave_eu_comb.add   = (eu_speriph_plug_req == 2'b10) ? eu_speriph_plug_add[1]   : eu_speriph_plug_add[0];
  assign speriph_slave_eu_comb.wen   = (eu_speriph_plug_req == 2'b10) ? eu_speriph_plug_wen[1]   : eu_speriph_plug_wen[0];
  assign speriph_slave_eu_comb.wdata = (eu_speriph_plug_req == 2'b10) ? eu_speriph_plug_wdata[1] : eu_speriph_plug_wdata[0];
  assign speriph_slave_eu_comb.be    = (eu_speriph_plug_req == 2'b10) ? eu_speriph_plug_be[1]    : eu_speriph_plug_be[0];
  assign speriph_slave_eu_comb.id    = (eu_speriph_plug_req == 2'b10) ? eu_speriph_plug_id[1]    : eu_speriph_plug_id[0];


  event_unit_top #(
    .NB_CORES     ( NB_CORES   ),
    .NB_BARR      ( NB_CORES   ),
    .PER_ID_WIDTH ( NB_CORES+1 ),
    .EVNT_WIDTH   ( EVNT_WIDTH )
  ) event_unit_flex_i (
    .clk_i                  ( clk_i                  ),
    .rst_ni                 ( rst_ni                 ),
    .test_mode_i            ( test_mode_i            ),

    .acc_events_i           ( s_acc_events           ),
    .dma_events_i           ( s_dma_events           ),
    .mailbox_evt_i          ( mailbox_evt_i          ),  
    .timer_events_i         ( s_timer_events         ),
    .cluster_events_i       ( s_cluster_events       ),


    .core_irq_id_o          ( irq_id_o               ),
    .core_irq_ack_id_i      ( irq_ack_id_i           ),
    .core_irq_req_o         ( irq_req_o              ),
    .core_irq_ack_i         ( irq_ack_i              ),
    .dbg_req_i              ( dbg_req_i              ),
    .core_dbg_req_o         ( dbg_req_o              ),


    .core_busy_i            ( core_busy_i            ),
    .core_clock_en_o        ( core_clk_en_o          ),
    
    .speriph_slave          ( speriph_slave_eu_comb  ),
    .eu_direct_link         ( core_eu_direct_link    ),
    
    .soc_periph_evt_valid_i ( soc_periph_evt_valid_i ),
    .soc_periph_evt_ready_o ( soc_periph_evt_ready_o ),
    .soc_periph_evt_data_i  ( soc_periph_evt_data_i  )
  );

  //********************************************************
    //******************** DMA CL CONFIG PORT ****************
    //********************************************************

    assign speriph_slave[SPER_DMA_CL_ID].gnt     = dma_cfg_master.gnt;
    assign speriph_slave[SPER_DMA_CL_ID].r_rdata = dma_cfg_master.r_rdata;
    assign speriph_slave[SPER_DMA_CL_ID].r_opc   = dma_cfg_master.r_opc;
    assign speriph_slave[SPER_DMA_CL_ID].r_id    = dma_cfg_master.r_id;
    assign speriph_slave[SPER_DMA_CL_ID].r_valid = dma_cfg_master.r_valid;

    assign dma_cfg_master.req   = speriph_slave[SPER_DMA_CL_ID].req;
    assign dma_cfg_master.add   = speriph_slave[SPER_DMA_CL_ID].add;
    assign dma_cfg_master.wen   = speriph_slave[SPER_DMA_CL_ID].wen;
    assign dma_cfg_master.wdata = speriph_slave[SPER_DMA_CL_ID].wdata;
    assign dma_cfg_master.be    = speriph_slave[SPER_DMA_CL_ID].be;
    assign dma_cfg_master.id    = speriph_slave[SPER_DMA_CL_ID].id;

    //********************************************************
    //******************** HW ACC  ***************************
    //********************************************************

    assign speriph_slave[SPER_HWPE_ID].gnt     = hwpe_cfg_master.gnt;
    assign speriph_slave[SPER_HWPE_ID].r_rdata = hwpe_cfg_master.r_rdata;
    assign speriph_slave[SPER_HWPE_ID].r_opc   = hwpe_cfg_master.r_opc;
    assign speriph_slave[SPER_HWPE_ID].r_id    = hwpe_cfg_master.r_id;
    assign speriph_slave[SPER_HWPE_ID].r_valid = hwpe_cfg_master.r_valid;

    assign hwpe_cfg_master.req   = speriph_slave[SPER_HWPE_ID].req;
    assign hwpe_cfg_master.add   = speriph_slave[SPER_HWPE_ID].add;
    assign hwpe_cfg_master.wen   = speriph_slave[SPER_HWPE_ID].wen;
    assign hwpe_cfg_master.wdata = speriph_slave[SPER_HWPE_ID].wdata;
    assign hwpe_cfg_master.be    = speriph_slave[SPER_HWPE_ID].be;
    assign hwpe_cfg_master.id    = speriph_slave[SPER_HWPE_ID].id;

    assign speriph_slave[SPER_DECOMP_ID].gnt     =    '0;
    assign speriph_slave[SPER_DECOMP_ID].r_rdata =  '0;
    assign speriph_slave[SPER_DECOMP_ID].r_opc   = '0;
    assign speriph_slave[SPER_DECOMP_ID].r_id    = '0;
    assign speriph_slave[SPER_DECOMP_ID].r_valid = '0;

  if (!FEATURE_DEMUX_MAPPED) begin : gen_eu_not_demux_mapped
    for (genvar i=0;i< NB_CORES; i++) begin : gen_eu_not_demux_mapped_cores
      assign core_eu_direct_link[i].gnt     = 1'b0;
      assign core_eu_direct_link[i].r_rdata = 32'h0000_0000;
      assign core_eu_direct_link[i].r_valid = 1'b0;
      assign core_eu_direct_link[i].r_opc   = 1'b0;
    end
  end

  //********************************************************
  //******************** icache_ctrl_unit ******************
  //********************************************************

  if (PRI_ICACHE) begin : gen_pri_icache_ctrl
    hier_icache_ctrl_unit_wrap #(
      .NB_CACHE_BANKS(NB_CACHE_BANKS),
      .NB_CORES(NB_CORES),
      .ID_WIDTH(NB_CORES+NB_MPERIPHS)
    ) icache_ctrl_unit_i (
      .clk_i                      ( clk_i                           ),
      .rst_ni                     ( rst_ni                          ),

      .speriph_slave              ( speriph_slave[SPER_ICACHE_CTRL] ),
      .IC_ctrl_unit_bus_pri       ( IC_ctrl_unit_bus_pri            ),
      .IC_ctrl_unit_bus_main      ( IC_ctrl_unit_bus_main           ),
      .enable_l1_l15_prefetch_o   ( enable_l1_l15_prefetch_o        )
    );

  end else begin : gen_no_pri_icache_ctrl
    for (genvar i = 0; i < NB_CACHE_BANKS; i++) begin : gen_banks
      assign IC_ctrl_unit_bus_main[i].ctrl_req_enable = 1'b0;
      assign IC_ctrl_unit_bus_main[i].ctrl_req_disable = 1'b0;
      assign IC_ctrl_unit_bus_main[i].ctrl_flush_req = 1'b0;
      assign IC_ctrl_unit_bus_main[i].icache_is_private = 1'b0;
      assign IC_ctrl_unit_bus_main[i].sel_flush_req = 1'b0;
      assign IC_ctrl_unit_bus_main[i].sel_flush_addr = '0;
      assign IC_ctrl_unit_bus_main[i].ctrl_clear_regs = 1'b0;
      assign IC_ctrl_unit_bus_main[i].ctrl_enable_regs = 1'b0;
    end
    for (genvar i = 0; i < NB_CORES; i++) begin : gen_cores
      assign IC_ctrl_unit_bus_pri[i].bypass_req = 1'b0;
      assign IC_ctrl_unit_bus_pri[i].flush_req = 1'b0;
      assign IC_ctrl_unit_bus_pri[i].ctrl_clear_regs = 1'b0;
      assign IC_ctrl_unit_bus_pri[i].ctrl_enable_regs = 1'b0;
      assign IC_ctrl_unit_bus_pri[i].sel_flush_req = 1'b0;
    end
    assign special_core_icache_cfg_o = 1'b0;
    assign enable_l1_l15_prefetch_o = '0;
  end

  if (MP_ICACHE) begin : gen_mp_icache_ctrl
    mp_pf_icache_ctrl_unit #(
      .NB_CACHE_BANKS ( NB_CACHE_BANKS       ),
      .NB_CORES       ( NB_CORES             ),
      .ID_WIDTH       ( NB_CORES+NB_MPERIPHS )
    ) icache_ctrl_unit_i (
      .clk_i                  ( clk_i                           ),
      .rst_ni                 ( rst_ni                          ),
      .speriph_slave          ( speriph_slave[SPER_ICACHE_CTRL] ),
      .IC_ctrl_unit_master_if ( IC_ctrl_unit_bus_mp             ),
      .pf_event_o             (                                 )
    );

  end else begin : gen_no_mp_icache_ctrl
    assign IC_ctrl_unit_bus_mp.bypass_req = 1'b0;
    assign IC_ctrl_unit_bus_mp.flush_req = 1'b0;
    assign IC_ctrl_unit_bus_mp.sel_flush_req = 1'b0;
    assign IC_ctrl_unit_bus_mp.sel_flush_addr = '0;
    assign IC_ctrl_unit_bus_mp.ctrl_clear_regs = 1'b0;
    assign IC_ctrl_unit_bus_mp.ctrl_enable_regs = 1'b0;
  end

  if (SP_ICACHE) begin : gen_sp_icache_ctrl
    sp_icache_ctrl_unit #(
      .NB_CACHE_BANKS (NB_CACHE_BANKS),
      .NB_CORES       (NB_CORES),
      .ID_WIDTH       (NB_CORES+NB_MPERIPHS)
    ) icache_ctrl_unit_i (
      .clk_i                  ( clk_i                           ),
      .rst_ni                 ( rst_ni                          ),

      .speriph_slave          ( speriph_slave[SPER_ICACHE_CTRL] ),
      .IC_ctrl_unit_master_if ( IC_ctrl_unit_bus_sp             ),
      .L0_ctrl_unit_master_if ( L0_ctrl_unit_bus_sp             )
    );

  end else begin : gen_no_sp_icache_ctrl
    for (genvar i = 0; i < NB_CACHE_BANKS; i++) begin : gen_banks
      assign IC_ctrl_unit_bus_sp[i].ctrl_req_enable = 1'b0;
      assign IC_ctrl_unit_bus_sp[i].ctrl_req_disable = 1'b0;
      assign IC_ctrl_unit_bus_sp[i].ctrl_flush_req = 1'b0;
      assign IC_ctrl_unit_bus_sp[i].icache_is_private = 1'b0;
      assign IC_ctrl_unit_bus_sp[i].sel_flush_req = 1'b0;
      assign IC_ctrl_unit_bus_sp[i].sel_flush_addr = '0;
      assign IC_ctrl_unit_bus_sp[i].ctrl_clear_regs = 1'b0;
      assign IC_ctrl_unit_bus_sp[i].ctrl_enable_regs = 1'b0;
    end
    for (genvar i = 0; i < NB_CORES; i++) begin : gen_cores
      assign L0_ctrl_unit_bus_sp[i].flush_FetchBuffer = 1'b0;
    end
  end

endmodule // cluster_peripherals
