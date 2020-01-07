// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


module soc_interconnect_wrap #(
    parameter N_L2_BANKS         = 4,
    parameter N_L2_BANKS_PRI     = 2,
    parameter N_HWPE_PORTS       = 4,
    parameter ADDR_MEM_WIDTH     = 12,
    parameter ADDR_MEM_PRI_WIDTH = 12,
    parameter AXI_32_ID_WIDTH    = 12,
    parameter AXI_32_USER_WIDTH  = 6,
    parameter ROM_ADDR_WIDTH     = 10,
    // 64 bit axi Interface
    parameter AXI_ADDR_WIDTH     = 32,
    parameter AXI_DATA_WIDTH     = 64,
    parameter AXI_STRB_WIDTH     = 8,
    parameter AXI_USER_WIDTH     = 6,
    parameter AXI_ID_WIDTH       = 7
) (
    input logic              clk_i,
    input logic              rstn_i,
    input logic              test_en_i,
    XBAR_TCDM_BUS.Slave      lint_fc_data,
    XBAR_TCDM_BUS.Slave      lint_fc_instr,
    XBAR_TCDM_BUS.Slave      lint_udma_tx,
    XBAR_TCDM_BUS.Slave      lint_udma_rx,
    XBAR_TCDM_BUS.Slave      lint_debug,
    XBAR_TCDM_BUS.Slave      lint_hwpe [N_HWPE_PORTS-1:0],
    AXI_BUS.Slave            axi_from_cluster,
    AXI_BUS.Master           axi_to_cluster,
    APB_BUS.Master           apb_periph_bus,
    UNICAD_MEM_BUS_32.Master mem_l2_bus[N_L2_BANKS-1:0],
    UNICAD_MEM_BUS_32.Master mem_l2_pri_bus[N_L2_BANKS_PRI-1:0],
    UNICAD_MEM_BUS_32.Master mem_rom_bus
);

    logic [N_L2_BANKS-1:0][31:0]                       mem_wdata;
    logic [N_L2_BANKS-1:0][ADDR_MEM_WIDTH-1:0]         mem_add;
    logic [N_L2_BANKS-1:0]                             mem_csn;
    logic [N_L2_BANKS-1:0]                             mem_wen;
    logic [N_L2_BANKS-1:0][3:0]                        mem_be;
    logic [N_L2_BANKS-1:0][31:0]                       mem_rdata;

    logic [N_L2_BANKS_PRI-1:0][31:0]                   mem_pri_wdata;
    logic [N_L2_BANKS_PRI-1:0][ADDR_MEM_PRI_WIDTH-1:0] mem_pri_add;
    logic [N_L2_BANKS_PRI-1:0]                         mem_pri_csn;
    logic [N_L2_BANKS_PRI-1:0]                         mem_pri_wen;
    logic [N_L2_BANKS_PRI-1:0][3:0]                    mem_pri_be;
    logic [N_L2_BANKS_PRI-1:0][31:0]                   mem_pri_rdata;

    // accelerator interface - must be unrolled
    logic [N_HWPE_PORTS-1:0]       s_lint_hwpe_req;
    logic [N_HWPE_PORTS-1:0][31:0] s_lint_hwpe_add;
    logic [N_HWPE_PORTS-1:0]       s_lint_hwpe_wen;
    logic [N_HWPE_PORTS-1:0][31:0] s_lint_hwpe_wdata;
    logic [N_HWPE_PORTS-1:0][3:0]  s_lint_hwpe_be;
    logic [N_HWPE_PORTS-1:0]       s_lint_hwpe_gnt;
    logic [N_HWPE_PORTS-1:0]       s_lint_hwpe_r_valid;
    logic [N_HWPE_PORTS-1:0][31:0] s_lint_hwpe_r_rdata;
    logic [N_HWPE_PORTS-1:0] s_lint_hwpe_r_opc;

    genvar i;

    generate

        for(i=0; i<N_HWPE_PORTS; i++)
        begin : HWPE_BINDING
            assign s_lint_hwpe_req   [i] = lint_hwpe[i].req;
            assign s_lint_hwpe_add   [i] = lint_hwpe[i].add;
            assign s_lint_hwpe_wen   [i] = lint_hwpe[i].wen;
            assign s_lint_hwpe_wdata [i] = lint_hwpe[i].wdata;
            assign s_lint_hwpe_be    [i] = lint_hwpe[i].be;
            assign lint_hwpe[i].gnt     = s_lint_hwpe_gnt     [i];
            assign lint_hwpe[i].r_valid = s_lint_hwpe_r_valid [i];
            assign lint_hwpe[i].r_rdata = s_lint_hwpe_r_rdata [i];
            assign lint_hwpe[i].r_opc   = s_lint_hwpe_r_opc   [i];
        end

        for(i=0; i<N_L2_BANKS; i++)
        begin : L2_BUS_BINDING
            assign mem_l2_bus[i].csn                     =  mem_csn[i]; // invert the csn because req is active high and csn is active low
            assign mem_l2_bus[i].add[ADDR_MEM_WIDTH-1:0] =  mem_add[i];
            assign mem_l2_bus[i].wen                     =  mem_wen[i];
            assign mem_l2_bus[i].wdata                   =  mem_wdata[i];
            assign mem_l2_bus[i].be                      =  mem_be[i];
            assign mem_rdata[i]                          =  mem_l2_bus[i].rdata;
        end

        for(i=0; i<N_L2_BANKS_PRI; i++)
        begin : L2_BUS_PRI_BINDING
            assign mem_l2_pri_bus[i].csn                     =  mem_pri_csn[i];
            assign mem_l2_pri_bus[i].add[ADDR_MEM_WIDTH-1:0] =  mem_pri_add[i];
            assign mem_l2_pri_bus[i].wen                     =  mem_pri_wen[i];
            assign mem_l2_pri_bus[i].wdata                   =  mem_pri_wdata[i];
            assign mem_l2_pri_bus[i].be                      =  mem_pri_be[i];
            assign mem_pri_rdata[i]                          =  mem_l2_pri_bus[i].rdata;
        end

    endgenerate

    soc_interconnect #(
        .N_L2_BANKS        ( N_L2_BANKS         ),
        .ADDR_L2_WIDTH     ( ADDR_MEM_WIDTH     ),
        .N_HWPE_PORTS      ( N_HWPE_PORTS       ),

        .AXI_32_ID_WIDTH   ( AXI_32_ID_WIDTH    ),
        .AXI_32_USER_WIDTH ( AXI_32_USER_WIDTH  ),

        .AXI_ADDR_WIDTH    ( AXI_ADDR_WIDTH     ),
        .AXI_DATA_WIDTH    ( AXI_DATA_WIDTH     ),
        .AXI_STRB_WIDTH    ( AXI_STRB_WIDTH     ),
        .AXI_USER_WIDTH    ( AXI_USER_WIDTH     ),
        .AXI_ID_WIDTH      ( AXI_ID_WIDTH       ),

        .N_L2_BANKS_PRI    ( N_L2_BANKS_PRI     ),
        .ADDR_L2_PRI_WIDTH ( ADDR_MEM_PRI_WIDTH ),
        .ROM_ADDR_WIDTH    ( ROM_ADDR_WIDTH     )
    ) i_soc_interconnect (
        .clk                    ( clk_i                                         ),
        .rst_n                  ( rstn_i                                        ),
        .test_en_i              ( test_en_i                                     ),

        .L2_D_o                 ( mem_wdata                                     ),
        .L2_A_o                 ( mem_add                                       ),
        .L2_CEN_o               ( mem_csn                                       ),
        .L2_WEN_o               ( mem_wen                                       ),
        .L2_BE_o                ( mem_be                                        ),
        .L2_Q_i                 ( mem_rdata                                     ),

        .L2_pri_D_o             ( mem_pri_wdata                                 ),
        .L2_pri_A_o             ( mem_pri_add                                   ),
        .L2_pri_CEN_o           ( mem_pri_csn                                   ),
        .L2_pri_WEN_o           ( mem_pri_wen                                   ),
        .L2_pri_BE_o            ( mem_pri_be                                    ),
        .L2_pri_Q_i             ( mem_pri_rdata                                 ),

        //RISC DATA PORT
        .FC_DATA_req_i          ( lint_fc_data.req                              ),
        .FC_DATA_add_i          ( lint_fc_data.add                              ),
        .FC_DATA_wen_i          ( lint_fc_data.wen                              ),
        .FC_DATA_wdata_i        ( lint_fc_data.wdata                            ),
        .FC_DATA_be_i           ( lint_fc_data.be                               ),
        .FC_DATA_aux_i          ( '0                                            ),
        .FC_DATA_gnt_o          ( lint_fc_data.gnt                              ),
        .FC_DATA_r_aux_o        (                                               ),
        .FC_DATA_r_valid_o      ( lint_fc_data.r_valid                          ),
        .FC_DATA_r_rdata_o      ( lint_fc_data.r_rdata                          ),
        .FC_DATA_r_opc_o        ( lint_fc_data.r_opc                            ),

        // RISC INSTR PORT
        .FC_INSTR_req_i         ( lint_fc_instr.req                             ),
        .FC_INSTR_add_i         ( lint_fc_instr.add                             ),
        .FC_INSTR_wen_i         ( lint_fc_instr.wen                             ),
        .FC_INSTR_wdata_i       ( lint_fc_instr.wdata                           ),
        .FC_INSTR_be_i          ( lint_fc_instr.be                              ),
        .FC_INSTR_aux_i         ( '0                                            ),
        .FC_INSTR_gnt_o         ( lint_fc_instr.gnt                             ),
        .FC_INSTR_r_aux_o       (                                               ),
        .FC_INSTR_r_valid_o     ( lint_fc_instr.r_valid                         ),
        .FC_INSTR_r_rdata_o     ( lint_fc_instr.r_rdata                         ),
        .FC_INSTR_r_opc_o       ( lint_fc_instr.r_opc                           ),

        // UDMA TX
        .UDMA_TX_req_i          ( lint_udma_tx.req                              ),
        .UDMA_TX_add_i          ( lint_udma_tx.add                              ),
        .UDMA_TX_wen_i          ( lint_udma_tx.wen                              ),
        .UDMA_TX_wdata_i        ( lint_udma_tx.wdata                            ),
        .UDMA_TX_be_i           ( lint_udma_tx.be                               ),
        .UDMA_TX_aux_i          ( '0                                            ),
        .UDMA_TX_gnt_o          ( lint_udma_tx.gnt                              ),
        .UDMA_TX_r_aux_o        (                                               ),
        .UDMA_TX_r_valid_o      ( lint_udma_tx.r_valid                          ),
        .UDMA_TX_r_rdata_o      ( lint_udma_tx.r_rdata                          ),
        .UDMA_TX_r_opc_o        ( lint_udma_tx.r_opc                            ),

        // UDMA RX
        .UDMA_RX_req_i          ( lint_udma_rx.req                              ),
        .UDMA_RX_add_i          ( lint_udma_rx.add                              ),
        .UDMA_RX_wen_i          ( lint_udma_rx.wen                              ),
        .UDMA_RX_wdata_i        ( lint_udma_rx.wdata                            ),
        .UDMA_RX_be_i           ( lint_udma_rx.be                               ),
        .UDMA_RX_aux_i          ( '0                                            ),
        .UDMA_RX_gnt_o          ( lint_udma_rx.gnt                              ),
        .UDMA_RX_r_aux_o        (                                               ),
        .UDMA_RX_r_valid_o      ( lint_udma_rx.r_valid                          ),
        .UDMA_RX_r_rdata_o      ( lint_udma_rx.r_rdata                          ),
        .UDMA_RX_r_opc_o        ( lint_udma_rx.r_opc                            ),

        // DBG
        .DBG_RX_req_i           ( lint_debug.req                                ),
        .DBG_RX_add_i           ( lint_debug.add                                ),
        .DBG_RX_wen_i           ( lint_debug.wen                                ),
        .DBG_RX_wdata_i         ( lint_debug.wdata                              ),
        .DBG_RX_be_i            ( lint_debug.be                                 ),
        .DBG_RX_aux_i           ( '0                                            ),
        .DBG_RX_gnt_o           ( lint_debug.gnt                                ),
        .DBG_RX_r_aux_o         (                                               ),
        .DBG_RX_r_valid_o       ( lint_debug.r_valid                            ),
        .DBG_RX_r_rdata_o       ( lint_debug.r_rdata                            ),
        .DBG_RX_r_opc_o         ( lint_debug.r_opc                              ),

        // HWPE
        .HWPE_req_i             ( s_lint_hwpe_req                               ),
        .HWPE_add_i             ( s_lint_hwpe_add                               ),
        .HWPE_wen_i             ( s_lint_hwpe_wen                               ),
        .HWPE_wdata_i           ( s_lint_hwpe_wdata                             ),
        .HWPE_be_i              ( s_lint_hwpe_be                                ),
        .HWPE_aux_i             ( '0                                            ),
        .HWPE_gnt_o             ( s_lint_hwpe_gnt                               ),
        .HWPE_r_aux_o           (                                               ),
        .HWPE_r_valid_o         ( s_lint_hwpe_r_valid                           ),
        .HWPE_r_rdata_o         ( s_lint_hwpe_r_rdata                           ),
        .HWPE_r_opc_o           ( s_lint_hwpe_r_opc                             ),

        // AXI INTERFACE (FROM CLUSTER)
        .AXI_Slave_aw_addr_i    ( axi_from_cluster.aw_addr                      ),
        .AXI_Slave_aw_prot_i    ( axi_from_cluster.aw_prot                      ),
        .AXI_Slave_aw_region_i  ( axi_from_cluster.aw_region                    ),
        .AXI_Slave_aw_len_i     ( axi_from_cluster.aw_len                       ),
        .AXI_Slave_aw_size_i    ( axi_from_cluster.aw_size                      ),
        .AXI_Slave_aw_burst_i   ( axi_from_cluster.aw_burst                     ),
        .AXI_Slave_aw_lock_i    ( axi_from_cluster.aw_lock                      ),
        .AXI_Slave_aw_cache_i   ( axi_from_cluster.aw_cache                     ),
        .AXI_Slave_aw_qos_i     ( axi_from_cluster.aw_qos                       ),
        .AXI_Slave_aw_id_i      ( axi_from_cluster.aw_id[AXI_ID_WIDTH-1:0]      ),
        .AXI_Slave_aw_user_i    ( axi_from_cluster.aw_user[AXI_USER_WIDTH-1:0]  ),
        .AXI_Slave_aw_valid_i   ( axi_from_cluster.aw_valid                     ),
        .AXI_Slave_aw_ready_o   ( axi_from_cluster.aw_ready                     ),
        // ADDRESS READ CHANNEL
        .AXI_Slave_ar_addr_i    ( axi_from_cluster.ar_addr                      ),
        .AXI_Slave_ar_prot_i    ( axi_from_cluster.ar_prot                      ),
        .AXI_Slave_ar_region_i  ( axi_from_cluster.ar_region                    ),
        .AXI_Slave_ar_len_i     ( axi_from_cluster.ar_len                       ),
        .AXI_Slave_ar_size_i    ( axi_from_cluster.ar_size                      ),
        .AXI_Slave_ar_burst_i   ( axi_from_cluster.ar_burst                     ),
        .AXI_Slave_ar_lock_i    ( axi_from_cluster.ar_lock                      ),
        .AXI_Slave_ar_cache_i   ( axi_from_cluster.ar_cache                     ),
        .AXI_Slave_ar_qos_i     ( axi_from_cluster.ar_qos                       ),
        .AXI_Slave_ar_id_i      ( axi_from_cluster.ar_id[AXI_ID_WIDTH-1:0]      ),
        .AXI_Slave_ar_user_i    ( axi_from_cluster.ar_user[AXI_USER_WIDTH-1:0]  ),
        .AXI_Slave_ar_valid_i   ( axi_from_cluster.ar_valid                     ),
        .AXI_Slave_ar_ready_o   ( axi_from_cluster.ar_ready                     ),
        // WRITE CHANNEL
        .AXI_Slave_w_user_i     ( axi_from_cluster.w_user[AXI_USER_WIDTH-1:0]   ),
        .AXI_Slave_w_data_i     ( axi_from_cluster.w_data                       ),
        .AXI_Slave_w_strb_i     ( axi_from_cluster.w_strb                       ),
        .AXI_Slave_w_last_i     ( axi_from_cluster.w_last                       ),
        .AXI_Slave_w_valid_i    ( axi_from_cluster.w_valid                      ),
        .AXI_Slave_w_ready_o    ( axi_from_cluster.w_ready                      ),
        // WRITE RESPONSE CHANNEL
        .AXI_Slave_b_id_o       ( axi_from_cluster.b_id[AXI_ID_WIDTH-1:0]       ),
        .AXI_Slave_b_resp_o     ( axi_from_cluster.b_resp                       ),
        .AXI_Slave_b_user_o     ( axi_from_cluster.b_user[AXI_USER_WIDTH-1:0]   ),
        .AXI_Slave_b_valid_o    ( axi_from_cluster.b_valid                      ),
        .AXI_Slave_b_ready_i    ( axi_from_cluster.b_ready                      ),
        // READ CHANNEL
        .AXI_Slave_r_id_o       ( axi_from_cluster.r_id[AXI_ID_WIDTH-1:0]       ),
        .AXI_Slave_r_user_o     ( axi_from_cluster.r_user[AXI_USER_WIDTH-1:0]   ),
        .AXI_Slave_r_data_o     ( axi_from_cluster.r_data                       ),
        .AXI_Slave_r_resp_o     ( axi_from_cluster.r_resp                       ),
        .AXI_Slave_r_last_o     ( axi_from_cluster.r_last                       ),
        .AXI_Slave_r_valid_o    ( axi_from_cluster.r_valid                      ),
        .AXI_Slave_r_ready_i    ( axi_from_cluster.r_ready                      ),

        // BRIDGES
        // LINT TO APB
        .APB_PADDR_o            ( apb_periph_bus.paddr                          ),
        .APB_PWDATA_o           ( apb_periph_bus.pwdata                         ),
        .APB_PWRITE_o           ( apb_periph_bus.pwrite                         ),
        .APB_PSEL_o             ( apb_periph_bus.psel                           ),
        .APB_PENABLE_o          ( apb_periph_bus.penable                        ),
        .APB_PRDATA_i           ( apb_periph_bus.prdata                         ),
        .APB_PREADY_i           ( apb_periph_bus.pready                         ),
        .APB_PSLVERR_i          ( apb_periph_bus.pslverr                        ),

        // ROM binding --> no need of Flow control, already handled in fc_interconnect
        .rom_csn_o              ( mem_rom_bus.csn                               ),
        .rom_add_o              ( mem_rom_bus.add[ROM_ADDR_WIDTH-1:0]           ),
        .rom_rdata_i            ( mem_rom_bus.rdata                             ),

        // LINT TO AXI
        // ---------------------------------------------------------
        // AXI TARG Port Declarations ------------------------------
        // ---------------------------------------------------------
        .AXI_Master_aw_addr_o   ( axi_to_cluster.aw_addr                        ),
        .AXI_Master_aw_prot_o   ( axi_to_cluster.aw_prot                        ),
        .AXI_Master_aw_region_o ( axi_to_cluster.aw_region                      ),
        .AXI_Master_aw_len_o    ( axi_to_cluster.aw_len                         ),
        .AXI_Master_aw_size_o   ( axi_to_cluster.aw_size                        ),
        .AXI_Master_aw_burst_o  ( axi_to_cluster.aw_burst                       ),
        .AXI_Master_aw_lock_o   ( axi_to_cluster.aw_lock                        ),
        .AXI_Master_aw_cache_o  ( axi_to_cluster.aw_cache                       ),
        .AXI_Master_aw_qos_o    ( axi_to_cluster.aw_qos                         ),
        .AXI_Master_aw_id_o     ( axi_to_cluster.aw_id[AXI_32_ID_WIDTH-1:0]     ),
        .AXI_Master_aw_user_o   ( axi_to_cluster.aw_user[AXI_32_USER_WIDTH-1:0] ),
        .AXI_Master_aw_valid_o  ( axi_to_cluster.aw_valid                       ),
        .AXI_Master_aw_ready_i  ( axi_to_cluster.aw_ready                       ),
        // ADDRESS READ CHANNEL
        .AXI_Master_ar_addr_o   ( axi_to_cluster.ar_addr                        ),
        .AXI_Master_ar_prot_o   ( axi_to_cluster.ar_prot                        ),
        .AXI_Master_ar_region_o ( axi_to_cluster.ar_region                      ),
        .AXI_Master_ar_len_o    ( axi_to_cluster.ar_len                         ),
        .AXI_Master_ar_size_o   ( axi_to_cluster.ar_size                        ),
        .AXI_Master_ar_burst_o  ( axi_to_cluster.ar_burst                       ),
        .AXI_Master_ar_lock_o   ( axi_to_cluster.ar_lock                        ),
        .AXI_Master_ar_cache_o  ( axi_to_cluster.ar_cache                       ),
        .AXI_Master_ar_qos_o    ( axi_to_cluster.ar_qos                         ),
        .AXI_Master_ar_id_o     ( axi_to_cluster.ar_id[AXI_32_ID_WIDTH-1:0]     ),
        .AXI_Master_ar_user_o   ( axi_to_cluster.ar_user[AXI_32_USER_WIDTH-1:0] ),
        .AXI_Master_ar_valid_o  ( axi_to_cluster.ar_valid                       ),
        .AXI_Master_ar_ready_i  ( axi_to_cluster.ar_ready                       ),
        // WRITE CHANNEL
        .AXI_Master_w_user_o    ( axi_to_cluster.w_user[AXI_32_USER_WIDTH-1:0]  ),
        .AXI_Master_w_data_o    ( axi_to_cluster.w_data                         ),
        .AXI_Master_w_strb_o    ( axi_to_cluster.w_strb                         ),
        .AXI_Master_w_last_o    ( axi_to_cluster.w_last                         ),
        .AXI_Master_w_valid_o   ( axi_to_cluster.w_valid                        ),
        .AXI_Master_w_ready_i   ( axi_to_cluster.w_ready                        ),
        // WRITE RESPONSE CHANNEL
        .AXI_Master_b_id_i      ( axi_to_cluster.b_id[AXI_32_ID_WIDTH-1:0]      ),
        .AXI_Master_b_resp_i    ( axi_to_cluster.b_resp                         ),
        .AXI_Master_b_user_i    ( axi_to_cluster.b_user[AXI_32_USER_WIDTH-1:0]  ),
        .AXI_Master_b_valid_i   ( axi_to_cluster.b_valid                        ),
        .AXI_Master_b_ready_o   ( axi_to_cluster.b_ready                        ),
        // READ CHANNEL
        .AXI_Master_r_id_i      ( axi_to_cluster.r_id[AXI_32_ID_WIDTH-1:0]      ),
        .AXI_Master_r_user_i    ( axi_to_cluster.r_user[AXI_32_USER_WIDTH-1:0]  ),
        .AXI_Master_r_data_i    ( axi_to_cluster.r_data                         ),
        .AXI_Master_r_resp_i    ( axi_to_cluster.r_resp                         ),
        .AXI_Master_r_last_i    ( axi_to_cluster.r_last                         ),
        .AXI_Master_r_valid_i   ( axi_to_cluster.r_valid                        ),
        .AXI_Master_r_ready_o   ( axi_to_cluster.r_ready                        )
    );

endmodule

