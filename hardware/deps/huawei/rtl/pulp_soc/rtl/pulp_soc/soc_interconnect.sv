// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


module soc_interconnect #(
    parameter USE_AXI           = 1,
    parameter ADDR_WIDTH        = 32,
    parameter N_HWPE_PORTS      = 4,
    parameter N_MASTER_32       = 5+N_HWPE_PORTS,
    parameter N_MASTER_AXI_64   = 1,
    parameter DATA_WIDTH        = 32,
    parameter BE_WIDTH          = DATA_WIDTH/8,
    parameter ID_WIDTH          = N_MASTER_32+N_MASTER_AXI_64*4,
    parameter AUX_WIDTH         = 8,
    parameter N_L2_BANKS        = 4,
    parameter N_L2_BANKS_PRI    = 2,
    parameter ADDR_L2_WIDTH     = 12,
    parameter ADDR_L2_PRI_WIDTH = 12,
    parameter ROM_ADDR_WIDTH    = 10,
    // AXI PARAMS
    // 32 bit axi Interface
    parameter AXI_32_ID_WIDTH   = 12,
    parameter AXI_32_USER_WIDTH = 6,
    // 64 bit axi Interface
    parameter AXI_ADDR_WIDTH    = 32,
    parameter AXI_DATA_WIDTH    = 64,
    parameter AXI_STRB_WIDTH    = 8,
    parameter AXI_USER_WIDTH    = 6,
    parameter AXI_ID_WIDTH      = 7
) (
    input  logic                                                clk,
    input  logic                                                rst_n,
    input  logic                                                test_en_i,
    output logic [N_L2_BANKS-1:0]     [DATA_WIDTH-1:0]          L2_D_o,
    output logic [N_L2_BANKS-1:0]     [ADDR_L2_WIDTH-1:0]       L2_A_o,
    output logic [N_L2_BANKS-1:0]                               L2_CEN_o,
    output logic [N_L2_BANKS-1:0]                               L2_WEN_o,
    output logic [N_L2_BANKS-1:0]     [BE_WIDTH-1:0]            L2_BE_o,
    input  logic [N_L2_BANKS-1:0]     [DATA_WIDTH-1:0]          L2_Q_i,
    //RISC DATA PORT
    input  logic                                                FC_DATA_req_i,
    input  logic [ADDR_WIDTH-1:0]                               FC_DATA_add_i,
    input  logic                                                FC_DATA_wen_i,
    input  logic [DATA_WIDTH-1:0]                               FC_DATA_wdata_i,
    input  logic [BE_WIDTH-1:0]                                 FC_DATA_be_i,
    input  logic [AUX_WIDTH-1:0]                                FC_DATA_aux_i,
    output logic                                                FC_DATA_gnt_o,
    output logic [AUX_WIDTH-1:0]                                FC_DATA_r_aux_o,
    output logic                                                FC_DATA_r_valid_o,
    output logic [DATA_WIDTH-1:0]                               FC_DATA_r_rdata_o,
    output logic                                                FC_DATA_r_opc_o,
    // RISC INSTR PORT
    input  logic                                                FC_INSTR_req_i,
    input  logic [ADDR_WIDTH-1:0]                               FC_INSTR_add_i,
    input  logic                                                FC_INSTR_wen_i,
    input  logic [DATA_WIDTH-1:0]                               FC_INSTR_wdata_i,
    input  logic [BE_WIDTH-1:0]                                 FC_INSTR_be_i,
    input  logic [AUX_WIDTH-1:0]                                FC_INSTR_aux_i,
    output logic                                                FC_INSTR_gnt_o,
    output logic [AUX_WIDTH-1:0]                                FC_INSTR_r_aux_o,
    output logic                                                FC_INSTR_r_valid_o,
    output logic [DATA_WIDTH-1:0]                               FC_INSTR_r_rdata_o,
    output logic                                                FC_INSTR_r_opc_o,
    // UDMA TX
    input  logic                                                UDMA_TX_req_i,
    input  logic [ADDR_WIDTH-1:0]                               UDMA_TX_add_i,
    input  logic                                                UDMA_TX_wen_i,
    input  logic [DATA_WIDTH-1:0]                               UDMA_TX_wdata_i,
    input  logic [BE_WIDTH-1:0]                                 UDMA_TX_be_i,
    input  logic [AUX_WIDTH-1:0]                                UDMA_TX_aux_i,
    output logic                                                UDMA_TX_gnt_o,
    output logic [AUX_WIDTH-1:0]                                UDMA_TX_r_aux_o,
    output logic                                                UDMA_TX_r_valid_o,
    output logic [DATA_WIDTH-1:0]                               UDMA_TX_r_rdata_o,
    output logic                                                UDMA_TX_r_opc_o,
    // UDMA RX
    input  logic                                                UDMA_RX_req_i,
    input  logic [ADDR_WIDTH-1:0]                               UDMA_RX_add_i,
    input  logic                                                UDMA_RX_wen_i,
    input  logic [DATA_WIDTH-1:0]                               UDMA_RX_wdata_i,
    input  logic [BE_WIDTH-1:0]                                 UDMA_RX_be_i,
    input  logic [AUX_WIDTH-1:0]                                UDMA_RX_aux_i,
    output logic                                                UDMA_RX_gnt_o,
    output logic [AUX_WIDTH-1:0]                                UDMA_RX_r_aux_o,
    output logic                                                UDMA_RX_r_valid_o,
    output logic [DATA_WIDTH-1:0]                               UDMA_RX_r_rdata_o,
    output logic                                                UDMA_RX_r_opc_o,
    // DBG
    input  logic                                                DBG_RX_req_i,
    input  logic [ADDR_WIDTH-1:0]                               DBG_RX_add_i,
    input  logic                                                DBG_RX_wen_i,
    input  logic [DATA_WIDTH-1:0]                               DBG_RX_wdata_i,
    input  logic [BE_WIDTH-1:0]                                 DBG_RX_be_i,
    input  logic [AUX_WIDTH-1:0]                                DBG_RX_aux_i,
    output logic                                                DBG_RX_gnt_o,
    output logic [AUX_WIDTH-1:0]                                DBG_RX_r_aux_o,
    output logic                                                DBG_RX_r_valid_o,
    output logic [DATA_WIDTH-1:0]                               DBG_RX_r_rdata_o,
    output logic                                                DBG_RX_r_opc_o,
    // HWPE
    input  logic [N_HWPE_PORTS-1:0]                             HWPE_req_i,
    input  logic [N_HWPE_PORTS-1:0]   [ADDR_WIDTH-1:0]          HWPE_add_i,
    input  logic [N_HWPE_PORTS-1:0]                             HWPE_wen_i,
    input  logic [N_HWPE_PORTS-1:0]   [DATA_WIDTH-1:0]          HWPE_wdata_i,
    input  logic [N_HWPE_PORTS-1:0]   [BE_WIDTH-1:0]            HWPE_be_i,
    input  logic [N_HWPE_PORTS-1:0]   [AUX_WIDTH-1:0]           HWPE_aux_i,
    output logic [N_HWPE_PORTS-1:0]                             HWPE_gnt_o,
    output logic [N_HWPE_PORTS-1:0]   [AUX_WIDTH-1:0]           HWPE_r_aux_o,
    output logic [N_HWPE_PORTS-1:0]                             HWPE_r_valid_o,
    output logic [N_HWPE_PORTS-1:0]   [DATA_WIDTH-1:0]          HWPE_r_rdata_o,
    output logic [N_HWPE_PORTS-1:0]                             HWPE_r_opc_o,
    // AXI INTERFACE (FROM CLUSTER)
    input  logic [AXI_ADDR_WIDTH-1:0]                           AXI_Slave_aw_addr_i,
    input  logic [2:0]                                          AXI_Slave_aw_prot_i,
    input  logic [3:0]                                          AXI_Slave_aw_region_i,
    input  logic [7:0]                                          AXI_Slave_aw_len_i,
    input  logic [2:0]                                          AXI_Slave_aw_size_i,
    input  logic [1:0]                                          AXI_Slave_aw_burst_i,
    input  logic                                                AXI_Slave_aw_lock_i,
    input  logic [3:0]                                          AXI_Slave_aw_cache_i,
    input  logic [3:0]                                          AXI_Slave_aw_qos_i,
    input  logic [AXI_ID_WIDTH-1:0]                             AXI_Slave_aw_id_i,
    input  logic [AXI_USER_WIDTH-1:0]                           AXI_Slave_aw_user_i,
    input  logic                                                AXI_Slave_aw_valid_i,
    output logic                                                AXI_Slave_aw_ready_o,
    // ADDRESS READ CHANNEL
    input  logic [AXI_ADDR_WIDTH-1:0]                           AXI_Slave_ar_addr_i,
    input  logic [2:0]                                          AXI_Slave_ar_prot_i,
    input  logic [3:0]                                          AXI_Slave_ar_region_i,
    input  logic [7:0]                                          AXI_Slave_ar_len_i,
    input  logic [2:0]                                          AXI_Slave_ar_size_i,
    input  logic [1:0]                                          AXI_Slave_ar_burst_i,
    input  logic                                                AXI_Slave_ar_lock_i,
    input  logic [3:0]                                          AXI_Slave_ar_cache_i,
    input  logic [3:0]                                          AXI_Slave_ar_qos_i,
    input  logic [AXI_ID_WIDTH-1:0]                             AXI_Slave_ar_id_i,
    input  logic [AXI_USER_WIDTH-1:0]                           AXI_Slave_ar_user_i,
    input  logic                                                AXI_Slave_ar_valid_i,
    output logic                                                AXI_Slave_ar_ready_o,
    // WRITE CHANNEL
    input  logic [AXI_USER_WIDTH-1:0]                           AXI_Slave_w_user_i,
    input  logic [AXI_DATA_WIDTH-1:0]                           AXI_Slave_w_data_i,
    input  logic [AXI_STRB_WIDTH-1:0]                           AXI_Slave_w_strb_i,
    input  logic                                                AXI_Slave_w_last_i,
    input  logic                                                AXI_Slave_w_valid_i,
    output logic                                                AXI_Slave_w_ready_o,
    // WRITE RESPONSE CHANNEL
    output logic [AXI_ID_WIDTH-1:0]                             AXI_Slave_b_id_o,
    output logic [1:0]                                          AXI_Slave_b_resp_o,
    output logic [AXI_USER_WIDTH-1:0]                           AXI_Slave_b_user_o,
    output logic                                                AXI_Slave_b_valid_o,
    input  logic                                                AXI_Slave_b_ready_i,
    // READ CHANNEL
    output logic [AXI_ID_WIDTH-1:0]                             AXI_Slave_r_id_o,
    output logic [AXI_USER_WIDTH-1:0]                           AXI_Slave_r_user_o,
    output logic [AXI_DATA_WIDTH-1:0]                           AXI_Slave_r_data_o,
    output logic [1:0]                                          AXI_Slave_r_resp_o,
    output logic                                                AXI_Slave_r_last_o,
    output logic                                                AXI_Slave_r_valid_o,
    input  logic                                                AXI_Slave_r_ready_i,
    // BRIDGES
    // CH_0 --> APB
    output logic [ADDR_WIDTH-1:0]                               APB_PADDR_o,
    output logic [DATA_WIDTH-1:0]                               APB_PWDATA_o,
    output logic                                                APB_PWRITE_o,
    output logic                                                APB_PSEL_o,
    output logic                                                APB_PENABLE_o,
    input  logic [DATA_WIDTH-1:0]                               APB_PRDATA_i,
    input  logic                                                APB_PREADY_i,
    input  logic                                                APB_PSLVERR_i,
    // CH_1 --> AXI
    // ---------------------------------------------------------
    // AXI TARG Port Declarations ------------------------------
    // ---------------------------------------------------------
    //AXI write address bus -------------- // USED// -----------
    output logic [AXI_32_ID_WIDTH-1:0]                          AXI_Master_aw_id_o,
    output logic [ADDR_WIDTH-1:0]                               AXI_Master_aw_addr_o,
    output logic [7:0]                                          AXI_Master_aw_len_o,
    output logic [2:0]                                          AXI_Master_aw_size_o,
    output logic [1:0]                                          AXI_Master_aw_burst_o,
    output logic                                                AXI_Master_aw_lock_o,
    output logic [3:0]                                          AXI_Master_aw_cache_o,
    output logic [2:0]                                          AXI_Master_aw_prot_o,
    output logic [3:0]                                          AXI_Master_aw_region_o,
    output logic [AXI_32_USER_WIDTH-1:0]                        AXI_Master_aw_user_o,
    output logic [3:0]                                          AXI_Master_aw_qos_o,
    output logic                                                AXI_Master_aw_valid_o,
    input  logic                                                AXI_Master_aw_ready_i,
    // ---------------------------------------------------------
    //AXI write data bus -------------- // USED// --------------
    output logic [DATA_WIDTH-1:0]                               AXI_Master_w_data_o,
    output logic [BE_WIDTH-1:0]                                 AXI_Master_w_strb_o,
    output logic                                                AXI_Master_w_last_o,
    output logic [AXI_32_USER_WIDTH-1:0]                        AXI_Master_w_user_o,
    output logic                                                AXI_Master_w_valid_o,
    input  logic                                                AXI_Master_w_ready_i,
    // ---------------------------------------------------------
    //AXI write response bus -------------- // USED// ----------
    input  logic [AXI_32_ID_WIDTH-1:0]                          AXI_Master_b_id_i,
    input  logic [1:0]                                          AXI_Master_b_resp_i,
    input  logic                                                AXI_Master_b_valid_i,
    input  logic [AXI_32_USER_WIDTH-1:0]                        AXI_Master_b_user_i,
    output logic                                                AXI_Master_b_ready_o,
    // ---------------------------------------------------------
    //AXI read address bus -------------------------------------
    output logic [AXI_32_ID_WIDTH-1:0]                          AXI_Master_ar_id_o,
    output logic [ADDR_WIDTH-1:0]                               AXI_Master_ar_addr_o,
    output logic [7:0]                                          AXI_Master_ar_len_o,
    output logic [2:0]                                          AXI_Master_ar_size_o,
    output logic [1:0]                                          AXI_Master_ar_burst_o,
    output logic                                                AXI_Master_ar_lock_o,
    output logic [3:0]                                          AXI_Master_ar_cache_o,
    output logic [2:0]                                          AXI_Master_ar_prot_o,
    output logic [3:0]                                          AXI_Master_ar_region_o,
    output logic [AXI_32_USER_WIDTH-1:0]                        AXI_Master_ar_user_o,
    output logic [3:0]                                          AXI_Master_ar_qos_o,
    output logic                                                AXI_Master_ar_valid_o,
    input  logic                                                AXI_Master_ar_ready_i,
    // ---------------------------------------------------------
    //AXI read data bus ----------------------------------------
    input  logic [AXI_32_ID_WIDTH-1:0]                          AXI_Master_r_id_i,
    input  logic [DATA_WIDTH-1:0]                               AXI_Master_r_data_i,
    input  logic [1:0]                                          AXI_Master_r_resp_i,
    input  logic                                                AXI_Master_r_last_i,
    input  logic [AXI_32_USER_WIDTH-1:0]                        AXI_Master_r_user_i,
    input  logic                                                AXI_Master_r_valid_i,
    output logic                                                AXI_Master_r_ready_o,
    // CH_2 --> ROM
    output logic                                                rom_csn_o,
    output logic [ROM_ADDR_WIDTH-1:0]                           rom_add_o,
    input  logic [DATA_WIDTH-1:0]                               rom_rdata_i,
    // CH_3, CH_4 Private Mem Banks (L2)
    output logic [N_L2_BANKS_PRI-1:0] [DATA_WIDTH-1:0]          L2_pri_D_o,
    output logic [N_L2_BANKS_PRI-1:0] [ADDR_L2_PRI_WIDTH-1:0]   L2_pri_A_o,
    output logic [N_L2_BANKS_PRI-1:0]                           L2_pri_CEN_o,
    output logic [N_L2_BANKS_PRI-1:0]                           L2_pri_WEN_o,
    output logic [N_L2_BANKS_PRI-1:0] [BE_WIDTH-1:0]            L2_pri_BE_o,
    input  logic [N_L2_BANKS_PRI-1:0] [DATA_WIDTH-1:0]          L2_pri_Q_i
);

    localparam N_CH0 = N_MASTER_32      ;
    localparam N_CH1 = N_MASTER_AXI_64*4;

    localparam N_CH0_BRIDGE = N_CH0;
    localparam N_CH1_BRIDGE = N_CH1;

    localparam PER_ID_WIDTH = N_CH0_BRIDGE+N_CH1_BRIDGE;
    localparam N_PERIPHS    = 3+N_L2_BANKS_PRI         ;

    localparam L2_OFFSET_PRI = 15'h1000; // FIXME Put the right FORMULA

                                                                        // PRI_L2_CH1  //PRI_L2_CH0    //ROM          // AXI         // APB
    localparam logic [N_PERIPHS-1:0][ADDR_WIDTH-1:0] PER_START_ADDR = { 32'h1C00_8000, 32'h1C00_0000, 32'h1A00_0000,  32'h1000_0000, 32'h1A10_0000};
    localparam logic [N_PERIPHS-1:0][ADDR_WIDTH-1:0] PER_END_ADDR   = { 32'h1C01_0000, 32'h1C00_8000, 32'h1A04_0000,  32'h1040_0000, 32'h1A40_0000};

    localparam logic [ADDR_WIDTH-1:0] TCDM_START_ADDR = {32'h1C01_0000}; // Start of L2 interleaved
    localparam logic [ADDR_WIDTH-1:0] TCDM_END_ADDR   = {32'h1C08_2000}; // END of L2 interleaved

    logic [N_MASTER_32-1:0]                           FC_data_req_INT_32;
    logic [N_MASTER_32-1:0] [ADDR_WIDTH - 1:0]        FC_data_add_INT_32;
    logic [ADDR_WIDTH-1:0]                            FC_DATA_add_int;
    logic [N_MASTER_32-1:0]                           FC_data_wen_INT_32;
    logic [N_MASTER_32-1:0] [DATA_WIDTH - 1:0]        FC_data_wdata_INT_32;
    logic [N_MASTER_32-1:0] [BE_WIDTH - 1:0]          FC_data_be_INT_32;
    logic [N_MASTER_32-1:0] [AUX_WIDTH - 1:0]         FC_data_aux_INT_32;
    logic [N_MASTER_32-1:0]                           FC_data_gnt_INT_32;
    logic [N_MASTER_32-1:0] [AUX_WIDTH-1:0]           FC_data_r_aux_INT_32;
    logic [N_MASTER_32-1:0]                           FC_data_r_valid_INT_32;
    logic [N_MASTER_32-1:0] [DATA_WIDTH - 1:0]        FC_data_r_rdata_INT_32;
    logic [N_MASTER_32-1:0] FC_data_r_opc_INT_32;

    logic [N_MASTER_AXI_64*4-1:0]                     AXI_data_req_INT_64;
    logic [N_MASTER_AXI_64*4-1:0] [ADDR_WIDTH - 1:0]  AXI_data_add_INT_64;
    logic [N_MASTER_AXI_64*4-1:0]                     AXI_data_wen_INT_64;
    logic [N_MASTER_AXI_64*4-1:0] [DATA_WIDTH - 1:0]  AXI_data_wdata_INT_64;
    logic [N_MASTER_AXI_64*4-1:0] [BE_WIDTH - 1:0]    AXI_data_be_INT_64;
    logic [N_MASTER_AXI_64*4-1:0] [AUX_WIDTH - 1:0]   AXI_data_aux_INT_64;
    logic [N_MASTER_AXI_64*4-1:0]                     AXI_data_gnt_INT_64;
    logic [N_MASTER_AXI_64*4-1:0] [AUX_WIDTH-1:0]     AXI_data_r_aux_INT_64;
    logic [N_MASTER_AXI_64*4-1:0]                     AXI_data_r_valid_INT_64;
    logic [N_MASTER_AXI_64*4-1:0] [DATA_WIDTH - 1:0]  AXI_data_r_rdata_INT_64;
    logic [N_MASTER_AXI_64*4-1:0] AXI_data_r_opc_INT_64;

    logic [N_CH0+N_CH1-1:0]                           PER_data_req_DEM_2_L2_XBAR;
    logic [N_CH0+N_CH1-1:0][ADDR_WIDTH-1:0]           PER_data_add_DEM_2_L2_XBAR;
    logic [N_CH0+N_CH1-1:0]                           PER_data_wen_DEM_2_L2_XBAR;
    logic [N_CH0+N_CH1-1:0][DATA_WIDTH-1:0]           PER_data_wdata_DEM_2_L2_XBAR;
    logic [N_CH0+N_CH1-1:0][BE_WIDTH-1:0]             PER_data_be_DEM_2_L2_XBAR;
    logic [N_CH0+N_CH1-1:0][AUX_WIDTH-1:0]            PER_data_aux_DEM_2_L2_XBAR;
    logic [N_CH0+N_CH1-1:0] PER_data_gnt_DEM_2_L2_XBAR;

    logic [N_CH0+N_CH1-1:0]                           PER_data_r_valid_DEM_2_L2_XBAR;
    logic [N_CH0+N_CH1-1:0][DATA_WIDTH-1:0]           PER_data_r_rdata_DEM_2_L2_XBAR;
    logic [N_CH0+N_CH1-1:0]                           PER_data_r_opc_DEM_2_L2_XBAR;
    logic [N_CH0+N_CH1-1:0][AUX_WIDTH-1:0]            PER_data_r_aux_DEM_2_L2_XBAR;

    // ---------------- BRIDGE SIDE --------------------------
    // Req --> to Mem
    logic [N_PERIPHS-1:0]                             PER_data_req_TO_BRIDGE;
    logic [N_PERIPHS-1:0][ADDR_WIDTH-1:0]             PER_data_add_TO_BRIDGE;
    logic [N_PERIPHS-1:0]                             PER_data_wen_TO_BRIDGE;
    logic [N_PERIPHS-1:0][DATA_WIDTH-1:0]             PER_data_wdata_TO_BRIDGE;
    logic [N_PERIPHS-1:0][BE_WIDTH-1:0]               PER_data_be_TO_BRIDGE;
    logic [N_PERIPHS-1:0][PER_ID_WIDTH-1:0]           PER_data_ID_TO_BRIDGE;
    logic [N_PERIPHS-1:0][AUX_WIDTH-1:0]              PER_data_aux_TO_BRIDGE;
    logic [N_PERIPHS-1:0] PER_data_gnt_TO_BRIDGE;

    // Resp        --> From Mem
    logic [N_PERIPHS-1:0][DATA_WIDTH-1:0]             PER_data_r_rdata_TO_BRIDGE;
    logic [N_PERIPHS-1:0]                             PER_data_r_valid_TO_BRIDGE;
    logic [N_PERIPHS-1:0][PER_ID_WIDTH-1:0]           PER_data_r_ID_TO_BRIDGE;
    logic [N_PERIPHS-1:0]                             PER_data_r_opc_TO_BRIDGE;
    logic [N_PERIPHS-1:0][AUX_WIDTH-1:0]              PER_data_r_aux_TO_BRIDGE;

    logic [N_CH0 + N_CH1-1:0][DATA_WIDTH-1:0]         TCDM_data_wdata_DEM_TO_XBAR;
    logic [N_CH0 + N_CH1-1:0][ADDR_WIDTH-1:0]         TCDM_data_add_DEM_TO_XBAR;
    logic [N_CH0 + N_CH1-1:0][ADDR_L2_WIDTH+$clog2(N_L2_BANKS)-1:0]      TCDM_data_add_DEM_TO_XBAR_resized;
    logic [N_CH0 + N_CH1-1:0]                         TCDM_data_req_DEM_TO_XBAR;
    logic [N_CH0 + N_CH1-1:0]                         TCDM_data_wen_DEM_TO_XBAR;
    logic [N_CH0 + N_CH1-1:0][BE_WIDTH-1:0]           TCDM_data_be_DEM_TO_XBAR;
    logic [N_CH0 + N_CH1-1:0]                         TCDM_data_gnt_DEM_TO_XBAR;
    logic [N_CH0 + N_CH1-1:0][DATA_WIDTH-1:0]         TCDM_data_r_rdata_DEM_TO_XBAR;
    logic [N_CH0 + N_CH1-1:0] TCDM_data_r_valid_DEM_TO_XBAR;


    logic [N_L2_BANKS-1:0][DATA_WIDTH-1:0]            TCDM_data_wdata_TO_MEM;
    logic [N_L2_BANKS-1:0][ADDR_L2_WIDTH-1:0]         TCDM_data_add_TO_MEM;
    logic [N_L2_BANKS-1:0]                            TCDM_data_req_TO_MEM;
    logic [N_L2_BANKS-1:0]                            TCDM_data_wen_TO_MEM;
    logic [N_L2_BANKS-1:0][BE_WIDTH-1:0]              TCDM_data_be_TO_MEM;
    logic [N_L2_BANKS-1:0][ID_WIDTH-1:0]              TCDM_data_ID_TO_MEM;
    logic [N_L2_BANKS-1:0][DATA_WIDTH-1:0]            TCDM_data_rdata_TO_MEM;
    logic [N_L2_BANKS-1:0]                            TCDM_data_rvalid_TO_MEM;
    logic [N_L2_BANKS-1:0][ID_WIDTH-1:0]              TCDM_data_rID_TO_MEM;

    // ROM BINDING
    assign rom_csn_o                     = ~PER_data_req_TO_BRIDGE[2];
    assign rom_add_o                     = PER_data_add_TO_BRIDGE[2];
    assign PER_data_r_rdata_TO_BRIDGE[2] = rom_rdata_i;

    assign PER_data_gnt_TO_BRIDGE[2]     = 1'b1;
    assign PER_data_r_opc_TO_BRIDGE[2]   = 1'b0;
    always_ff @(posedge clk or negedge rst_n)
    begin : proc_
       if(~rst_n)
       begin
           PER_data_r_valid_TO_BRIDGE[2] <= '0;
           PER_data_r_ID_TO_BRIDGE[2]    <= '0;
           PER_data_r_aux_TO_BRIDGE[2]   <= '0;
       end
       else
       begin
           PER_data_r_ID_TO_BRIDGE[2]    <= PER_data_ID_TO_BRIDGE[2];
           PER_data_r_valid_TO_BRIDGE[2] <= PER_data_req_TO_BRIDGE[2];
           PER_data_r_aux_TO_BRIDGE[2]   <= PER_data_aux_TO_BRIDGE[2];
       end
    end

    genvar k;
    generate
        // Private mem Binding
        for (k = 0; k< N_L2_BANKS_PRI; k++) begin
            assign L2_pri_D_o   [k] =  PER_data_wdata_TO_BRIDGE[k+3];
            assign L2_pri_A_o   [k] =  PER_data_add_TO_BRIDGE  [k+3][ADDR_L2_PRI_WIDTH+1:2];
            assign L2_pri_CEN_o [k] = ~PER_data_req_TO_BRIDGE  [k+3];
            assign L2_pri_WEN_o [k] =  PER_data_wen_TO_BRIDGE  [k+3];
            assign L2_pri_BE_o  [k] =  PER_data_be_TO_BRIDGE   [k+3];

            assign PER_data_r_rdata_TO_BRIDGE[k+3] = L2_pri_Q_i  [k];
            assign PER_data_gnt_TO_BRIDGE[k+3]     = 1'b1;
            assign PER_data_r_opc_TO_BRIDGE[k+3]   = '0;

            always_ff @(posedge clk or negedge rst_n)
            begin : proc_L2_CH_pri_rvalid_gen
                if(~rst_n) begin
                    PER_data_r_valid_TO_BRIDGE[k+3] <= '0;
                    PER_data_r_ID_TO_BRIDGE[k+3]    <= '0;
                    PER_data_r_aux_TO_BRIDGE[k+3]   <= '0;
                end
                else begin
                    PER_data_r_valid_TO_BRIDGE[k+3] <= PER_data_req_TO_BRIDGE[k+3];
                    PER_data_r_ID_TO_BRIDGE[k+3]    <= PER_data_ID_TO_BRIDGE[k+3];
                    PER_data_r_aux_TO_BRIDGE[k+3]   <= PER_data_aux_TO_BRIDGE[k+3];
                end
            end

        end
    endgenerate

    always_comb
    begin
        FC_DATA_add_int = FC_DATA_add_i;
        if(FC_DATA_add_i[31:20] == 12'h000)
            FC_DATA_add_int[31:20] = 12'h1C0;
    end

    assign FC_data_req_INT_32      =  {  FC_INSTR_req_i      ,  UDMA_TX_req_i     ,  UDMA_RX_req_i     , DBG_RX_req_i     , FC_DATA_req_i      };
    assign FC_data_add_INT_32      =  {  FC_INSTR_add_i      ,  UDMA_TX_add_i     ,  UDMA_RX_add_i     , DBG_RX_add_i     , FC_DATA_add_int    };
    assign FC_data_wen_INT_32      =  {  FC_INSTR_wen_i      ,  UDMA_TX_wen_i     ,  UDMA_RX_wen_i     , DBG_RX_wen_i     , FC_DATA_wen_i      };
    assign FC_data_wdata_INT_32    =  {  FC_INSTR_wdata_i    ,  UDMA_TX_wdata_i   ,  UDMA_RX_wdata_i   , DBG_RX_wdata_i   , FC_DATA_wdata_i    };
    assign FC_data_be_INT_32       =  {  FC_INSTR_be_i       ,  UDMA_TX_be_i      ,  UDMA_RX_be_i      , DBG_RX_be_i      , FC_DATA_be_i       };
    assign FC_data_aux_INT_32      =  {  FC_INSTR_aux_i      ,  UDMA_TX_aux_i     ,  UDMA_RX_aux_i     , DBG_RX_aux_i     , FC_DATA_aux_i      };
    assign                            {  FC_INSTR_gnt_o      ,  UDMA_TX_gnt_o     ,  UDMA_RX_gnt_o     , DBG_RX_gnt_o     , FC_DATA_gnt_o      } = FC_data_gnt_INT_32     ;
    assign                            {  FC_INSTR_r_aux_o    ,  UDMA_TX_r_aux_o   ,  UDMA_RX_r_aux_o   , DBG_RX_r_aux_o   , FC_DATA_r_aux_o    } = FC_data_r_aux_INT_32   ;
    assign                            {  FC_INSTR_r_valid_o  ,  UDMA_TX_r_valid_o ,  UDMA_RX_r_valid_o , DBG_RX_r_valid_o , FC_DATA_r_valid_o  } = FC_data_r_valid_INT_32 ;
    assign                            {  FC_INSTR_r_rdata_o  ,  UDMA_TX_r_rdata_o ,  UDMA_RX_r_rdata_o , DBG_RX_r_rdata_o , FC_DATA_r_rdata_o  } = FC_data_r_rdata_INT_32 ;
    assign                            {  FC_INSTR_r_opc_o    ,  UDMA_TX_r_opc_o   ,  UDMA_RX_r_opc_o   , DBG_RX_r_opc_o   , FC_DATA_r_opc_o    } = FC_data_r_opc_INT_32   ;

    // the accelerator is directly connected to the interleaved region
    assign TCDM_data_req_DEM_TO_XBAR   [N_CH0-1:N_CH0-N_HWPE_PORTS] =  HWPE_req_i;
    assign TCDM_data_add_DEM_TO_XBAR   [N_CH0-1:N_CH0-N_HWPE_PORTS] =  HWPE_add_i;
    assign TCDM_data_wen_DEM_TO_XBAR   [N_CH0-1:N_CH0-N_HWPE_PORTS] =  HWPE_wen_i;
    assign TCDM_data_wdata_DEM_TO_XBAR [N_CH0-1:N_CH0-N_HWPE_PORTS] =  HWPE_wdata_i;
    assign TCDM_data_be_DEM_TO_XBAR    [N_CH0-1:N_CH0-N_HWPE_PORTS] =  HWPE_be_i;
    assign HWPE_gnt_o      = TCDM_data_gnt_DEM_TO_XBAR     [N_CH0-1:N_CH0-N_HWPE_PORTS];
    assign HWPE_r_valid_o  = TCDM_data_r_valid_DEM_TO_XBAR [N_CH0-1:N_CH0-N_HWPE_PORTS];
    assign HWPE_r_rdata_o  = TCDM_data_r_rdata_DEM_TO_XBAR [N_CH0-1:N_CH0-N_HWPE_PORTS];

    genvar j;
    generate
        for(j=0;j<N_CH0+N_CH1;j++) begin
            assign TCDM_data_add_DEM_TO_XBAR_resized[j] = TCDM_data_add_DEM_TO_XBAR[j][ADDR_L2_WIDTH+$clog2(N_L2_BANKS)+2-1:2];
        end
    endgenerate

    // ██╗     ██████╗         ██╗  ██╗██████╗  █████╗ ██████╗
    // ██║     ╚════██╗        ╚██╗██╔╝██╔══██╗██╔══██╗██╔══██╗
    // ██║      █████╔╝         ╚███╔╝ ██████╔╝███████║██████╔╝
    // ██║     ██╔═══╝          ██╔██╗ ██╔══██╗██╔══██║██╔══██╗
    // ███████╗███████╗███████╗██╔╝ ██╗██████╔╝██║  ██║██║  ██║
    // ╚══════╝╚══════╝╚══════╝╚═╝  ╚═╝╚═════╝ ╚═╝  ╚═╝╚═╝  ╚═╝
    // out channels: 4 memory channels
    // in channels:  5 from FC( fc_instr, fc_data, udma_tx, udma_rx, debug_in) + 4 (AXI --> 2 for read, 2 for write)
    XBAR_L2 #(
        .N_CH0          ( N_CH0                            ),
        .N_CH1          ( N_CH1                            ),
        .N_SLAVE        ( N_L2_BANKS                       ),
        .ID_WIDTH       ( N_CH0+N_CH1                      ),

        //FRONT END PARAMS
        .ADDR_IN_WIDTH  ( ADDR_L2_WIDTH+$clog2(N_L2_BANKS) ),
        .DATA_WIDTH     ( DATA_WIDTH                       ),
        .BE_WIDTH       ( BE_WIDTH                         ),
        .ADDR_MEM_WIDTH ( ADDR_L2_WIDTH                    )
    ) XBAR_L2_i (
        // ---------------- MASTER CH0+CH1 SIDE  --------------------------
        .data_req_i     ( TCDM_data_req_DEM_TO_XBAR         ),
        .data_add_i     ( TCDM_data_add_DEM_TO_XBAR_resized ),
        .data_wen_i     ( TCDM_data_wen_DEM_TO_XBAR         ),
        .data_wdata_i   ( TCDM_data_wdata_DEM_TO_XBAR       ),
        .data_be_i      ( TCDM_data_be_DEM_TO_XBAR          ),
        .data_gnt_o     ( TCDM_data_gnt_DEM_TO_XBAR         ),
        .data_r_valid_o ( TCDM_data_r_valid_DEM_TO_XBAR     ),
        .data_r_rdata_o ( TCDM_data_r_rdata_DEM_TO_XBAR     ),

        // ---------------- MM_SIDE (Interleaved) --------------------------
        .data_req_o     ( TCDM_data_req_TO_MEM              ),
        .data_add_o     ( TCDM_data_add_TO_MEM              ),
        .data_wen_o     ( TCDM_data_wen_TO_MEM              ),
        .data_wdata_o   ( TCDM_data_wdata_TO_MEM            ),
        .data_be_o      ( TCDM_data_be_TO_MEM               ),
        .data_ID_o      ( TCDM_data_ID_TO_MEM               ),

        .data_r_rdata_i ( TCDM_data_rdata_TO_MEM            ),
        .data_r_valid_i ( TCDM_data_rvalid_TO_MEM           ),
        .data_r_ID_i    ( TCDM_data_rID_TO_MEM              ),

        .clk            ( clk                               ),
        .rst_n          ( rst_n                             )
    );

    // ██████╗ ██████╗ ██╗██████╗  ██████╗ ███████╗        ██╗  ██╗██████╗  █████╗ ██████╗
    // ██╔══██╗██╔══██╗██║██╔══██╗██╔════╝ ██╔════╝        ╚██╗██╔╝██╔══██╗██╔══██╗██╔══██╗
    // ██████╔╝██████╔╝██║██║  ██║██║  ███╗█████╗           ╚███╔╝ ██████╔╝███████║██████╔╝
    // ██╔══██╗██╔══██╗██║██║  ██║██║   ██║██╔══╝           ██╔██╗ ██╔══██╗██╔══██║██╔══██╗
    // ██████╔╝██║  ██║██║██████╔╝╚██████╔╝███████╗███████╗██╔╝ ██╗██████╔╝██║  ██║██║  ██║
    // ╚═════╝ ╚═╝  ╚═╝╚═╝╚═════╝  ╚═════╝ ╚══════╝╚══════╝╚═╝  ╚═╝╚═════╝ ╚═╝  ╚═╝╚═╝  ╚═╝
    // Full COnnectivity (Full crossbar)
    // out channels: 2 channels APB32 and AXI32
    // in channels:  2 from FC( fc_data, debug_in) + 4 (AXI --> 2 for read, 2 for write)
    XBAR_BRIDGE #(
        .N_CH0             ( N_CH0_BRIDGE                   ), // 2  --> Removed (FC_instr, udma_tx, udma_rx)
        .N_CH1             ( N_CH1_BRIDGE                   ), // 4  --> AXI64
        .N_SLAVE           ( N_PERIPHS                      ),
        .ID_WIDTH          ( PER_ID_WIDTH                   ),

        .AUX_WIDTH         ( AUX_WIDTH                      ),
        .ADDR_WIDTH        ( ADDR_WIDTH                     ),
        .DATA_WIDTH        ( DATA_WIDTH                     ),
        .BE_WIDTH          ( BE_WIDTH                       )
    ) XBAR_BRIDGE_i (
        .data_req_i        ( PER_data_req_DEM_2_L2_XBAR     ),
        .data_add_i        ( PER_data_add_DEM_2_L2_XBAR     ),
        .data_wen_i        ( PER_data_wen_DEM_2_L2_XBAR     ),
        .data_wdata_i      ( PER_data_wdata_DEM_2_L2_XBAR   ),
        .data_be_i         ( PER_data_be_DEM_2_L2_XBAR      ),
        .data_aux_i        ( PER_data_aux_DEM_2_L2_XBAR     ),
        .data_gnt_o        ( PER_data_gnt_DEM_2_L2_XBAR     ),
        .data_r_valid_o    ( PER_data_r_valid_DEM_2_L2_XBAR ),
        .data_r_rdata_o    ( PER_data_r_rdata_DEM_2_L2_XBAR ),
        .data_r_opc_o      ( PER_data_r_opc_DEM_2_L2_XBAR   ),
        .data_r_aux_o      ( PER_data_r_aux_DEM_2_L2_XBAR   ),

        .data_req_o        ( PER_data_req_TO_BRIDGE         ),
        .data_add_o        ( PER_data_add_TO_BRIDGE         ),
        .data_wen_o        ( PER_data_wen_TO_BRIDGE         ),
        .data_wdata_o      ( PER_data_wdata_TO_BRIDGE       ),
        .data_be_o         ( PER_data_be_TO_BRIDGE          ),
        .data_ID_o         ( PER_data_ID_TO_BRIDGE          ),
        .data_aux_o        ( PER_data_aux_TO_BRIDGE         ),
        .data_gnt_i        ( PER_data_gnt_TO_BRIDGE         ),

        .data_r_rdata_i    ( PER_data_r_rdata_TO_BRIDGE     ),
        .data_r_valid_i    ( PER_data_r_valid_TO_BRIDGE     ),
        .data_r_ID_i       ( PER_data_r_ID_TO_BRIDGE        ),
        .data_r_opc_i      ( PER_data_r_opc_TO_BRIDGE       ),
        .data_r_aux_i      ( PER_data_r_aux_TO_BRIDGE       ),

        .clk               ( clk                            ),
        .rst_n             ( rst_n                          ),

        .START_ADDR        ( PER_START_ADDR                 ),
        .END_ADDR          ( PER_END_ADDR                   )
    );

    genvar i;
    generate
        // ██╗     ██████╗      ████████╗ ██████╗██████╗ ███╗   ███╗        ██████╗ ███████╗███╗   ███╗██╗   ██╗██╗  ██╗
        // ██║     ╚════██╗     ╚══██╔══╝██╔════╝██╔══██╗████╗ ████║        ██╔══██╗██╔════╝████╗ ████║██║   ██║╚██╗██╔╝
        // ██║      █████╔╝        ██║   ██║     ██║  ██║██╔████╔██║        ██║  ██║█████╗  ██╔████╔██║██║   ██║ ╚███╔╝
        // ██║     ██╔═══╝         ██║   ██║     ██║  ██║██║╚██╔╝██║        ██║  ██║██╔══╝  ██║╚██╔╝██║██║   ██║ ██╔██╗
        // ███████╗███████╗███████╗██║   ╚██████╗██████╔╝██║ ╚═╝ ██║███████╗██████╔╝███████╗██║ ╚═╝ ██║╚██████╔╝██╔╝ ██╗
        // ╚══════╝╚══════╝╚══════╝╚═╝    ╚═════╝╚═════╝ ╚═╝     ╚═╝╚══════╝╚═════╝ ╚══════╝╚═╝     ╚═╝ ╚═════╝ ╚═╝  ╚═╝
        for(i=0; i<N_CH0-N_HWPE_PORTS; i++) begin : FC_DEMUX_32
            l2_tcdm_demux #(
                .ADDR_WIDTH ( ADDR_WIDTH ), //= 32,
                .DATA_WIDTH ( DATA_WIDTH ), //= 32,
                .BE_WIDTH   ( BE_WIDTH   ), //= DATA_WIDTH/8,
                .AUX_WIDTH  ( AUX_WIDTH  ), //=
                .N_PERIPHS  ( N_PERIPHS  )  //= 2
            ) DEMUX_MASTER_32 (
                .clk                 ( clk                                ),
                .rst_n               ( rst_n                              ),
                .test_en_i           ( test_en_i                          ),

                // CORE SIDE
                .data_req_i          ( FC_data_req_INT_32     [i]         ),
                .data_add_i          ( FC_data_add_INT_32     [i]         ),
                .data_wen_i          ( FC_data_wen_INT_32     [i]         ),
                .data_wdata_i        ( FC_data_wdata_INT_32   [i]         ),
                .data_be_i           ( FC_data_be_INT_32      [i]         ),
                .data_aux_i          ( FC_data_aux_INT_32     [i]         ),
                .data_gnt_o          ( FC_data_gnt_INT_32     [i]         ),
                .data_r_aux_o        ( FC_data_r_aux_INT_32   [i]         ),
                .data_r_valid_o      ( FC_data_r_valid_INT_32 [i]         ),
                .data_r_rdata_o      ( FC_data_r_rdata_INT_32 [i]         ),
                .data_r_opc_o        ( FC_data_r_opc_INT_32   [i]         ),

                // Interleaved Region
                .data_req_o_TDCM     ( TCDM_data_req_DEM_TO_XBAR      [i] ),
                .data_add_o_TDCM     ( TCDM_data_add_DEM_TO_XBAR      [i] ),
                .data_wen_o_TDCM     ( TCDM_data_wen_DEM_TO_XBAR      [i] ),
                .data_wdata_o_TDCM   ( TCDM_data_wdata_DEM_TO_XBAR    [i] ),
                .data_be_o_TDCM      ( TCDM_data_be_DEM_TO_XBAR       [i] ),
                .data_gnt_i_TDCM     ( TCDM_data_gnt_DEM_TO_XBAR      [i] ),
                .data_r_valid_i_TDCM ( TCDM_data_r_valid_DEM_TO_XBAR  [i] ),
                .data_r_rdata_i_TDCM ( TCDM_data_r_rdata_DEM_TO_XBAR  [i] ),

                // Memory Regions : Bridges
                .data_req_o_PER      ( PER_data_req_DEM_2_L2_XBAR     [i] ),
                .data_add_o_PER      ( PER_data_add_DEM_2_L2_XBAR     [i] ),
                .data_wen_o_PER      ( PER_data_wen_DEM_2_L2_XBAR     [i] ),
                .data_wdata_o_PER    ( PER_data_wdata_DEM_2_L2_XBAR   [i] ),
                .data_be_o_PER       ( PER_data_be_DEM_2_L2_XBAR      [i] ),
                .data_aux_o_PER      ( PER_data_aux_DEM_2_L2_XBAR     [i] ),
                .data_gnt_i_PER      ( PER_data_gnt_DEM_2_L2_XBAR     [i] ),
                .data_r_valid_i_PER  ( PER_data_r_valid_DEM_2_L2_XBAR [i] ),
                .data_r_rdata_i_PER  ( PER_data_r_rdata_DEM_2_L2_XBAR [i] ),
                .data_r_opc_i_PER    ( PER_data_r_opc_DEM_2_L2_XBAR   [i] ),
                .data_r_aux_i_PER    ( PER_data_r_aux_DEM_2_L2_XBAR   [i] ),

                .PER_START_ADDR      ( PER_START_ADDR                     ),
                .PER_END_ADDR        ( PER_END_ADDR                       ),
                .TCDM_START_ADDR     ( TCDM_START_ADDR                    ),
                .TCDM_END_ADDR       ( TCDM_END_ADDR                      )
            );
        end

        for(i=0; i<N_CH1; i++) begin : FC_DEMUX_64
            l2_tcdm_demux #(
                .ADDR_WIDTH ( ADDR_WIDTH ), //= 32,
                .DATA_WIDTH ( DATA_WIDTH ), //= 32,
                .BE_WIDTH   ( BE_WIDTH   ), //= DATA_WIDTH/8,
                .AUX_WIDTH  ( AUX_WIDTH  ), //=
                .N_PERIPHS  ( N_PERIPHS  )  //= 2
            ) DEMUX_AXI64 (
                .clk                 ( clk                                      ),
                .rst_n               ( rst_n                                    ),
                .test_en_i           ( test_en_i                                ),

                // CORE SIDE
                .data_req_i          ( AXI_data_req_INT_64     [i]              ),
                .data_add_i          ( AXI_data_add_INT_64     [i]              ),
                .data_wen_i          ( AXI_data_wen_INT_64     [i]              ),
                .data_wdata_i        ( AXI_data_wdata_INT_64   [i]              ),
                .data_be_i           ( AXI_data_be_INT_64      [i]              ),
                .data_aux_i          ( AXI_data_aux_INT_64     [i]              ),
                .data_gnt_o          ( AXI_data_gnt_INT_64     [i]              ),
                .data_r_aux_o        ( AXI_data_r_aux_INT_64   [i]              ),
                .data_r_valid_o      ( AXI_data_r_valid_INT_64 [i]              ),
                .data_r_rdata_o      ( AXI_data_r_rdata_INT_64 [i]              ),
                .data_r_opc_o        ( AXI_data_r_opc_INT_64   [i]              ),

                // Interleaved Region
                .data_req_o_TDCM     ( TCDM_data_req_DEM_TO_XBAR      [N_CH0+i] ),
                .data_add_o_TDCM     ( TCDM_data_add_DEM_TO_XBAR      [N_CH0+i] ),
                .data_wen_o_TDCM     ( TCDM_data_wen_DEM_TO_XBAR      [N_CH0+i] ),
                .data_wdata_o_TDCM   ( TCDM_data_wdata_DEM_TO_XBAR    [N_CH0+i] ),
                .data_be_o_TDCM      ( TCDM_data_be_DEM_TO_XBAR       [N_CH0+i] ),
                .data_gnt_i_TDCM     ( TCDM_data_gnt_DEM_TO_XBAR      [N_CH0+i] ),
                .data_r_valid_i_TDCM ( TCDM_data_r_valid_DEM_TO_XBAR  [N_CH0+i] ),
                .data_r_rdata_i_TDCM ( TCDM_data_r_rdata_DEM_TO_XBAR  [N_CH0+i] ),

                // Memory Regions : Bridges
                .data_req_o_PER      ( PER_data_req_DEM_2_L2_XBAR     [N_CH0+i] ),
                .data_add_o_PER      ( PER_data_add_DEM_2_L2_XBAR     [N_CH0+i] ),
                .data_wen_o_PER      ( PER_data_wen_DEM_2_L2_XBAR     [N_CH0+i] ),
                .data_wdata_o_PER    ( PER_data_wdata_DEM_2_L2_XBAR   [N_CH0+i] ),
                .data_be_o_PER       ( PER_data_be_DEM_2_L2_XBAR      [N_CH0+i] ),
                .data_aux_o_PER      ( PER_data_aux_DEM_2_L2_XBAR     [N_CH0+i] ),
                .data_gnt_i_PER      ( PER_data_gnt_DEM_2_L2_XBAR     [N_CH0+i] ),
                .data_r_valid_i_PER  ( PER_data_r_valid_DEM_2_L2_XBAR [N_CH0+i] ),
                .data_r_rdata_i_PER  ( PER_data_r_rdata_DEM_2_L2_XBAR [N_CH0+i] ),
                .data_r_opc_i_PER    ( PER_data_r_opc_DEM_2_L2_XBAR   [N_CH0+i] ),
                .data_r_aux_i_PER    ( PER_data_r_aux_DEM_2_L2_XBAR   [N_CH0+i] ),

                .PER_START_ADDR      ( PER_START_ADDR                           ),
                .PER_END_ADDR        ( PER_END_ADDR                             ),
                .TCDM_START_ADDR     ( TCDM_START_ADDR                          ),
                .TCDM_END_ADDR       ( TCDM_END_ADDR                            )
            );
        end
    endgenerate

// ███╗   ███╗███████╗███╗   ███╗         ██████╗██╗   ██╗████████╗
// ████╗ ████║██╔════╝████╗ ████║        ██╔════╝██║   ██║╚══██╔══╝
// ██╔████╔██║█████╗  ██╔████╔██║        ██║     ██║   ██║   ██║
// ██║╚██╔╝██║██╔══╝  ██║╚██╔╝██║        ██║     ██║   ██║   ██║
// ██║ ╚═╝ ██║███████╗██║ ╚═╝ ██║███████╗╚██████╗╚██████╔╝   ██║
// ╚═╝     ╚═╝╚══════╝╚═╝     ╚═╝╚══════╝ ╚═════╝ ╚═════╝    ╚═╝
    always_comb begin
        for(int unsigned i=0;i<N_L2_BANKS;i++) begin
            L2_D_o[i]   =  TCDM_data_wdata_TO_MEM[i];
            L2_A_o[i]   =  TCDM_data_add_TO_MEM[i]-L2_OFFSET_PRI;
            L2_CEN_o[i] = ~TCDM_data_req_TO_MEM[i];
            L2_WEN_o[i] =  TCDM_data_wen_TO_MEM[i];
            L2_BE_o[i]  =  TCDM_data_be_TO_MEM[i];
            TCDM_data_rdata_TO_MEM[i] = L2_Q_i[i];
        end
    end

    always_ff @(posedge clk, negedge rst_n)
    begin
        if(rst_n == 1'b0) begin
            for(int unsigned i=0;i<N_L2_BANKS;i++) begin
                TCDM_data_rID_TO_MEM[i]       <= '0;
                TCDM_data_rvalid_TO_MEM[i]    <= '0;
            end
        end
        else begin
            for (int unsigned  i=0;i<N_L2_BANKS;i++) begin
                if(TCDM_data_req_TO_MEM[i]) begin
                    TCDM_data_rID_TO_MEM[i]       <= TCDM_data_ID_TO_MEM[i];
                    TCDM_data_rvalid_TO_MEM[i]    <= 1'b1;
                end
                else begin
                    TCDM_data_rvalid_TO_MEM[i]    <= 1'b0;
                end
            end
        end
    end

// ██╗     ██╗███╗   ██╗████████╗     ██████╗          █████╗ ██████╗ ██████╗
// ██║     ██║████╗  ██║╚══██╔══╝     ╚════██╗        ██╔══██╗██╔══██╗██╔══██╗
// ██║     ██║██╔██╗ ██║   ██║         █████╔╝        ███████║██████╔╝██████╔╝
// ██║     ██║██║╚██╗██║   ██║        ██╔═══╝         ██╔══██║██╔═══╝ ██╔══██╗
// ███████╗██║██║ ╚████║   ██║███████╗███████╗███████╗██║  ██║██║     ██████╔╝
// ╚══════╝╚═╝╚═╝  ╚═══╝   ╚═╝╚══════╝╚══════╝╚══════╝╚═╝  ╚═╝╚═╝     ╚═════╝
    lint_2_apb #(
        .ADDR_WIDTH     ( ADDR_WIDTH                  ), // 32,
        .DATA_WIDTH     ( DATA_WIDTH                  ), // 32,
        .BE_WIDTH       ( BE_WIDTH                    ), // DATA_WIDTH/8,
        .ID_WIDTH       ( PER_ID_WIDTH                ), // 10,
        .AUX_WIDTH      ( AUX_WIDTH                   )  // 8
    ) lint_2_apb_i (
        .clk            ( clk                           ),
        .rst_n          ( rst_n                         ),
        .data_req_i     ( PER_data_req_TO_BRIDGE    [0] ),
        .data_add_i     ( PER_data_add_TO_BRIDGE    [0] ),
        .data_wen_i     ( PER_data_wen_TO_BRIDGE    [0] ),
        .data_wdata_i   ( PER_data_wdata_TO_BRIDGE  [0] ),
        .data_be_i      ( PER_data_be_TO_BRIDGE     [0] ),
        .data_aux_i     ( PER_data_aux_TO_BRIDGE    [0] ),
        .data_ID_i      ( PER_data_ID_TO_BRIDGE     [0] ),
        .data_gnt_o     ( PER_data_gnt_TO_BRIDGE    [0] ),
        // Resp
        .data_r_valid_o ( PER_data_r_valid_TO_BRIDGE[0] ),
        .data_r_rdata_o ( PER_data_r_rdata_TO_BRIDGE[0] ),
        .data_r_opc_o   ( PER_data_r_opc_TO_BRIDGE  [0] ),
        .data_r_aux_o   ( PER_data_r_aux_TO_BRIDGE  [0] ),
        .data_r_ID_o    ( PER_data_r_ID_TO_BRIDGE   [0] ),

        .master_PADDR   ( APB_PADDR_o                   ),
        .master_PWDATA  ( APB_PWDATA_o                  ),
        .master_PWRITE  ( APB_PWRITE_o                  ),
        .master_PSEL    ( APB_PSEL_o                    ),
        .master_PENABLE ( APB_PENABLE_o                 ),
        .master_PRDATA  ( APB_PRDATA_i                  ),
        .master_PREADY  ( APB_PREADY_i                  ),
        .master_PSLVERR ( APB_PSLVERR_i                 )
    );


    lint_2_axi #(
        .ADDR_WIDTH       ( ADDR_WIDTH        ),
        .DATA_WIDTH       ( DATA_WIDTH        ),
        .BE_WIDTH         ( BE_WIDTH          ),
        .ID_WIDTH         ( PER_ID_WIDTH      ),
        .USER_WIDTH       ( AXI_32_USER_WIDTH ),
        .AUX_WIDTH        ( AUX_WIDTH         ),
        .AXI_ID_WIDTH     ( AXI_32_ID_WIDTH   ),
        .REGISTERED_GRANT ( "FALSE"           )  // "TRUE"|"FALSE"
    ) i_lint_2_axi (
        // Clock and Reset
        .clk_i         ( clk                            ),
        .rst_ni        ( rst_n                          ),

        .data_req_i    ( PER_data_req_TO_BRIDGE    [1]  ),
        .data_addr_i   ( PER_data_add_TO_BRIDGE    [1]  ),
        .data_we_i     ( ~PER_data_wen_TO_BRIDGE   [1]  ),
        .data_wdata_i  ( PER_data_wdata_TO_BRIDGE  [1]  ),
        .data_be_i     ( PER_data_be_TO_BRIDGE     [1]  ),
        .data_aux_i    ( PER_data_aux_TO_BRIDGE    [1]  ),
        .data_ID_i     ( PER_data_ID_TO_BRIDGE     [1]  ),
        .data_gnt_o    ( PER_data_gnt_TO_BRIDGE    [1]  ),

        .data_rvalid_o ( PER_data_r_valid_TO_BRIDGE [1] ),
        .data_rdata_o  ( PER_data_r_rdata_TO_BRIDGE [1] ),
        .data_ropc_o   ( PER_data_r_opc_TO_BRIDGE   [1] ),
        .data_raux_o   ( PER_data_r_aux_TO_BRIDGE   [1] ),
        .data_rID_o    ( PER_data_r_ID_TO_BRIDGE    [1] ),
        // ---------------------------------------------------------
        // AXI TARG Port Declarations ------------------------------
        // ---------------------------------------------------------
        //AXI write address bus -------------- // USED// -----------
        .aw_id_o       ( AXI_Master_aw_id_o             ),
        .aw_addr_o     ( AXI_Master_aw_addr_o           ),
        .aw_len_o      ( AXI_Master_aw_len_o            ),
        .aw_size_o     ( AXI_Master_aw_size_o           ),
        .aw_burst_o    ( AXI_Master_aw_burst_o          ),
        .aw_lock_o     ( AXI_Master_aw_lock_o           ),
        .aw_cache_o    ( AXI_Master_aw_cache_o          ),
        .aw_prot_o     ( AXI_Master_aw_prot_o           ),
        .aw_region_o   ( AXI_Master_aw_region_o         ),
        .aw_user_o     ( AXI_Master_aw_user_o           ),
        .aw_qos_o      ( AXI_Master_aw_qos_o            ),
        .aw_valid_o    ( AXI_Master_aw_valid_o          ),
        .aw_ready_i    ( AXI_Master_aw_ready_i          ),
        // ---------------------------------------------------------

        //AXI write data bus -------------- // USED// --------------
        .w_data_o      ( AXI_Master_w_data_o            ),
        .w_strb_o      ( AXI_Master_w_strb_o            ),
        .w_last_o      ( AXI_Master_w_last_o            ),
        .w_user_o      ( AXI_Master_w_user_o            ),
        .w_valid_o     ( AXI_Master_w_valid_o           ),
        .w_ready_i     ( AXI_Master_w_ready_i           ),
        // ---------------------------------------------------------

        //AXI write response bus -------------- // USED// ----------
        .b_id_i        ( AXI_Master_b_id_i              ),
        .b_resp_i      ( AXI_Master_b_resp_i            ),
        .b_valid_i     ( AXI_Master_b_valid_i           ),
        .b_user_i      ( AXI_Master_b_user_i            ),
        .b_ready_o     ( AXI_Master_b_ready_o           ),
        // ---------------------------------------------------------

        //AXI read address bus -------------------------------------
        .ar_id_o       ( AXI_Master_ar_id_o             ),
        .ar_addr_o     ( AXI_Master_ar_addr_o           ),
        .ar_len_o      ( AXI_Master_ar_len_o            ),
        .ar_size_o     ( AXI_Master_ar_size_o           ),
        .ar_burst_o    ( AXI_Master_ar_burst_o          ),
        .ar_lock_o     ( AXI_Master_ar_lock_o           ),
        .ar_cache_o    ( AXI_Master_ar_cache_o          ),
        .ar_prot_o     ( AXI_Master_ar_prot_o           ),
        .ar_region_o   ( AXI_Master_ar_region_o         ),
        .ar_user_o     ( AXI_Master_ar_user_o           ),
        .ar_qos_o      ( AXI_Master_ar_qos_o            ),
        .ar_valid_o    ( AXI_Master_ar_valid_o          ),
        .ar_ready_i    ( AXI_Master_ar_ready_i          ),
        // ---------------------------------------------------------

        //AXI read data bus ----------------------------------------
        .r_id_i        ( AXI_Master_r_id_i              ),
        .r_data_i      ( AXI_Master_r_data_i            ),
        .r_resp_i      ( AXI_Master_r_resp_i            ),
        .r_last_i      ( AXI_Master_r_last_i            ),
        .r_user_i      ( AXI_Master_r_user_i            ),
        .r_valid_i     ( AXI_Master_r_valid_i           ),
        .r_ready_o     ( AXI_Master_r_ready_o           )
        // ---------------------------------------------------------
    );

        //  █████╗ ██╗  ██╗██╗        ██████╗         ██╗     ██╗███╗   ██╗████████╗
        // ██╔══██╗╚██╗██╔╝██║        ╚════██╗        ██║     ██║████╗  ██║╚══██╔══╝
        // ███████║ ╚███╔╝ ██║         █████╔╝        ██║     ██║██╔██╗ ██║   ██║
        // ██╔══██║ ██╔██╗ ██║        ██╔═══╝         ██║     ██║██║╚██╗██║   ██║
        // ██║  ██║██╔╝ ██╗██║███████╗███████╗███████╗███████╗██║██║ ╚████║   ██║
        // ╚═╝  ╚═╝╚═╝  ╚═╝╚═╝╚══════╝╚══════╝╚══════╝╚══════╝╚═╝╚═╝  ╚═══╝   ╚═╝
    axi64_2_lint32 #(
        .AXI_ADDR_WIDTH    ( AXI_ADDR_WIDTH ), //= 32,
        .AXI_DATA_WIDTH    ( AXI_DATA_WIDTH ), //= 64,
        .AXI_STRB_WIDTH    ( AXI_STRB_WIDTH ), //= 8,
        .AXI_USER_WIDTH    ( AXI_USER_WIDTH ), //= 6,
        .AXI_ID_WIDTH      ( AXI_ID_WIDTH   ), //= 7,
        .BUFF_DEPTH_SLICES ( 4              ), //= 4,
        .DATA_WIDTH        ( DATA_WIDTH     ), //= 64,
        .BE_WIDTH          ( BE_WIDTH       ), //= DATA_WIDTH/8,
        .ADDR_WIDTH        ( ADDR_WIDTH     ), //= 10
        .AUX_WIDTH         ( AUX_WIDTH      )
        ) axi64_2_lint32_i (
        // AXI GLOBAL SIGNALS
        .clk              ( clk                          ),
        .rst_n            ( rst_n                        ),
        .test_en_i        ( test_en_i                    ),
        // AXI INTERFACE
        .AW_ADDR_i        ( AXI_Slave_aw_addr_i          ),
        .AW_PROT_i        ( AXI_Slave_aw_prot_i          ),
        .AW_REGION_i      ( AXI_Slave_aw_region_i        ),
        .AW_LEN_i         ( AXI_Slave_aw_len_i           ),
        .AW_SIZE_i        ( AXI_Slave_aw_size_i          ),
        .AW_BURST_i       ( AXI_Slave_aw_burst_i         ),
        .AW_LOCK_i        ( AXI_Slave_aw_lock_i          ),
        .AW_CACHE_i       ( AXI_Slave_aw_cache_i         ),
        .AW_QOS_i         ( AXI_Slave_aw_qos_i           ),
        .AW_ID_i          ( AXI_Slave_aw_id_i            ),
        .AW_USER_i        ( AXI_Slave_aw_user_i          ),
        .AW_VALID_i       ( AXI_Slave_aw_valid_i         ),
        .AW_READY_o       ( AXI_Slave_aw_ready_o         ),
        // ADDRESS READ CHANNEL
        .AR_ADDR_i        ( AXI_Slave_ar_addr_i          ),
        .AR_PROT_i        ( AXI_Slave_ar_prot_i          ),
        .AR_REGION_i      ( AXI_Slave_ar_region_i        ),
        .AR_LEN_i         ( AXI_Slave_ar_len_i           ),
        .AR_SIZE_i        ( AXI_Slave_ar_size_i          ),
        .AR_BURST_i       ( AXI_Slave_ar_burst_i         ),
        .AR_LOCK_i        ( AXI_Slave_ar_lock_i          ),
        .AR_CACHE_i       ( AXI_Slave_ar_cache_i         ),
        .AR_QOS_i         ( AXI_Slave_ar_qos_i           ),
        .AR_ID_i          ( AXI_Slave_ar_id_i            ),
        .AR_USER_i        ( AXI_Slave_ar_user_i          ),
        .AR_VALID_i       ( AXI_Slave_ar_valid_i         ),
        .AR_READY_o       ( AXI_Slave_ar_ready_o         ),
        // WRITE CHANNEL
        .W_USER_i         ( AXI_Slave_w_user_i           ),
        .W_DATA_i         ( AXI_Slave_w_data_i           ),
        .W_STRB_i         ( AXI_Slave_w_strb_i           ),
        .W_LAST_i         ( AXI_Slave_w_last_i           ),
        .W_VALID_i        ( AXI_Slave_w_valid_i          ),
        .W_READY_o        ( AXI_Slave_w_ready_o          ),
        // WRITE RESPONSE CHANNEL
        .B_ID_o           ( AXI_Slave_b_id_o             ),
        .B_RESP_o         ( AXI_Slave_b_resp_o           ),
        .B_USER_o         ( AXI_Slave_b_user_o           ),
        .B_VALID_o        ( AXI_Slave_b_valid_o          ),
        .B_READY_i        ( AXI_Slave_b_ready_i          ),
        // READ CHANNEL
        .R_ID_o           ( AXI_Slave_r_id_o             ),
        .R_USER_o         ( AXI_Slave_r_user_o           ),
        .R_DATA_o         ( AXI_Slave_r_data_o           ),
        .R_RESP_o         ( AXI_Slave_r_resp_o           ),
        .R_LAST_o         ( AXI_Slave_r_last_o           ),
        .R_VALID_o        ( AXI_Slave_r_valid_o          ),
        .R_READY_i        ( AXI_Slave_r_ready_i          ),

        // LINT Interface - WRITE Request
        .data_W_req_o     ( AXI_data_req_INT_64  [1:0]   ),
        .data_W_gnt_i     ( AXI_data_gnt_INT_64  [1:0]   ),
        .data_W_wdata_o   ( AXI_data_wdata_INT_64[1:0]   ),
        .data_W_add_o     ( AXI_data_add_INT_64  [1:0]   ),
        .data_W_wen_o     ( AXI_data_wen_INT_64  [1:0]   ),
        .data_W_be_o      ( AXI_data_be_INT_64   [1:0]   ),
        .data_W_aux_o     ( AXI_data_aux_INT_64  [1:0]   ),

        // LINT Interface - Response
        .data_W_r_valid_i ( AXI_data_r_valid_INT_64[1:0] ),
        .data_W_r_rdata_i ( AXI_data_r_rdata_INT_64[1:0] ),
        .data_W_r_opc_i   ( AXI_data_r_opc_INT_64  [1:0] ),
        .data_W_r_aux_i   ( AXI_data_r_aux_INT_64  [1:0] ),

        // LINT Interface - READ Request
        .data_R_req_o     ( AXI_data_req_INT_64  [3:2]   ),
        .data_R_gnt_i     ( AXI_data_gnt_INT_64  [3:2]   ),
        .data_R_wdata_o   ( AXI_data_wdata_INT_64[3:2]   ),
        .data_R_add_o     ( AXI_data_add_INT_64  [3:2]   ),
        .data_R_wen_o     ( AXI_data_wen_INT_64  [3:2]   ),
        .data_R_be_o      ( AXI_data_be_INT_64   [3:2]   ),
        .data_R_aux_o     ( AXI_data_aux_INT_64  [3:2]   ),

        // LINT Interface - Responseesponse
        .data_R_r_valid_i ( AXI_data_r_valid_INT_64[3:2] ),
        .data_R_r_rdata_i ( AXI_data_r_rdata_INT_64[3:2] ),
        .data_R_r_opc_i   ( AXI_data_r_opc_INT_64  [3:2] ),
        .data_R_r_aux_i   ( AXI_data_r_aux_INT_64  [3:2] )
    );

endmodule
