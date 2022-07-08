`include "axi/assign.svh"
`include "axi/typedef.svh"

module top 
    import pulp_cluster_package::*; 
    import apu_package::*; 
    import apu_core_package::*;
(
    input   logic   clk_i       , // operation clock
    input   logic   rst_ni      , // operation clock reset(async-reset)

    input   logic   ref_clk_i     // reference clock for timer
);

    // ============================================================
    // declare dut parameter
    // ============================================================
    // cluster parameters
    parameter bit ASYNC_INTF          = 1'b0;     // RV-CORE is on async-clock domain
    parameter int NB_CORES            = 8;        // # of RV-CORE
    parameter int NB_HWACC_PORTS      = 0;        // # of HWPE
    parameter int NB_DMAS             = 4;        // # of DMA channel for TDCM
    parameter int NB_EXT2MEM          = 2;        // # of bank that accessable at a once from External
    parameter int NB_MPERIPHS         = 1;        // # of master peri for interconnect_wrap -- NOTE::DO NOT TOUCH
    parameter int NB_SPERIPHS         = 8;        // # of slape peri for interconnect_wrap
    parameter bit CLUSTER_ALIAS       = 1'b1;     // RV-CORE attribution
    parameter int CLUSTER_ALIAS_BASE  = 12'h1B0;  // RV-CORE attribution
    parameter int TCDM_SIZE           = 256*1024;                // [B], must be 2**N
    parameter int NB_TCDM_BANKS       = 16;                      // must be 2**N
    parameter int TCDM_BANK_SIZE      = TCDM_SIZE/NB_TCDM_BANKS; // [B]
    parameter int TCDM_NUM_ROWS       = TCDM_BANK_SIZE/4;        // [words]
    parameter bit XNE_PRESENT         = 0;                       // set to 1 if XNE is present in the cluster

    // I$ parameters
    parameter int SET_ASSOCIATIVE           = 4;
    parameter int NB_CACHE_BANKS            = 4;
    parameter int CACHE_LINE                = 1;
    parameter int CACHE_SIZE                = 4096;
    parameter int ICACHE_DATA_WIDTH         = 128;
    parameter int L2_SIZE                   = 256*1024;
    parameter bit USE_REDUCED_TAG           = 1'b1;

    // core parameters
    parameter bit DEM_PER_BEFORE_TCDM_TS  = 1'b0;
    parameter int ROM_BOOT_ADDR           = 32'h1A000000;
    parameter int BOOT_ADDR               = 32'h1C000000;
    parameter int INSTR_RDATA_WIDTH       = 128;

    // AXI parameters
    //parameter int AXI_ADDR_WIDTH        = 32;
    parameter int AXI_ADDR_WIDTH        = 64;
    parameter int AXI_DATA_C2S_WIDTH    = 64;
    parameter int AXI_DATA_S2C_WIDTH    = 64;
    parameter int AXI_USER_WIDTH        = 6;
    parameter int AXI_ID_IN_WIDTH       = 4;
    parameter int AXI_ID_OUT_WIDTH      = 6;
    parameter int AXI_STRB_C2S_WIDTH    = AXI_DATA_C2S_WIDTH/8;
    parameter int AXI_STRB_S2C_WIDTH    = AXI_DATA_S2C_WIDTH/8;
    parameter int DC_SLICE_BUFFER_WIDTH = 8;

    // TCDM and log interconnect parameters
    parameter int DATA_WIDTH      = 32;
    parameter int ADDR_WIDTH      = 32;
    parameter int BE_WIDTH        = DATA_WIDTH/8;
    parameter int TEST_SET_BIT    = 20;                       // bit used to indicate a test-and-set operation during a load in TCDM
    parameter int ADDR_MEM_WIDTH  = $clog2(TCDM_BANK_SIZE/4); // WORD address width per TCDM bank (the word width is 32 bits)

    // DMA parameters
    parameter int NB_DMA_STREAMS   = 4; // # of DMA master channel
    parameter int NB_OUTSND_BURSTS = 8;

    // peripheral and periph interconnect parameters
    parameter int LOG_CLUSTER     = 5;  // unused
    parameter int PE_ROUTING_LSB  = 10; // LSB used as routing BIT in periph interco
    parameter int PE_ROUTING_MSB  = 13; // MSB used as routing BIT in periph interco
    parameter int EVNT_WIDTH      = 8;  // size of the event bus
    parameter int REMAP_ADDRESS   = 0;  // for cluster virtualization
    // ============================================================


    // ============================================================
    // declare dut io
    // ============================================================
    bit                               pmu_mem_pwdn_i;

    bit   [3:0]                       base_addr_i;

    bit                               test_mode_i;

    bit                               en_sa_boot_i;

    bit   [5:0]                       cluster_id_i;

    bit                               fetch_en_i;

    bit                               eoc_o;

    bit                               busy_o;

    bit   [DC_SLICE_BUFFER_WIDTH-1:0] ext_events_writetoken_i;
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] ext_events_readpointer_o;
    bit              [EVNT_WIDTH-1:0] ext_events_dataasync_i;

    bit                               dma_pe_evt_ack_i;
    bit                               dma_pe_evt_valid_o;

    bit                               dma_pe_irq_ack_i;
    bit                               dma_pe_irq_valid_o;

    bit                               pf_evt_ack_i;
    bit                               pf_evt_valid_o;

    // AXI4 SLAVE
    //***************************************
    // WRITE ADDRESS CHANNEL
    bit   [AXI_ADDR_WIDTH-1:0]        data_slave_aw_addr_i;
    bit   [2:0]                       data_slave_aw_prot_i;
    bit   [3:0]                       data_slave_aw_region_i;
    bit   [7:0]                       data_slave_aw_len_i;
    bit   [2:0]                       data_slave_aw_size_i;
    bit   [1:0]                       data_slave_aw_burst_i;
    bit                               data_slave_aw_lock_i;
    bit   [5:0]                       data_slave_aw_atop_i;
    bit   [3:0]                       data_slave_aw_cache_i;
    bit   [3:0]                       data_slave_aw_qos_i;
    bit   [AXI_ID_IN_WIDTH-1:0]       data_slave_aw_id_i;
    bit   [AXI_USER_WIDTH-1:0]        data_slave_aw_user_i;
    // used if ASYNC_INTF
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_aw_writetoken_i;
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_aw_readpointer_o;
    // used if !ASYNC_INTF
    bit                               data_slave_aw_valid_i;
    bit                               data_slave_aw_ready_o;

    // READ ADDRESS CHANNEL
    bit   [AXI_ADDR_WIDTH-1:0]        data_slave_ar_addr_i;
    bit   [2:0]                       data_slave_ar_prot_i;
    bit   [3:0]                       data_slave_ar_region_i;
    bit   [7:0]                       data_slave_ar_len_i;
    bit   [2:0]                       data_slave_ar_size_i;
    bit   [1:0]                       data_slave_ar_burst_i;
    bit                               data_slave_ar_lock_i;
    bit   [3:0]                       data_slave_ar_cache_i;
    bit   [3:0]                       data_slave_ar_qos_i;
    bit   [AXI_ID_IN_WIDTH-1:0]       data_slave_ar_id_i;
    bit   [AXI_USER_WIDTH-1:0]        data_slave_ar_user_i;
    // used if ASYNC_INTF
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_ar_writetoken_i;
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_ar_readpointer_o;
    // used if !ASYNC_INTF
    bit                               data_slave_ar_valid_i;
    bit                               data_slave_ar_ready_o;

    // WRITE DATA CHANNEL
    bit   [AXI_DATA_S2C_WIDTH-1:0]    data_slave_w_data_i;
    bit   [AXI_STRB_S2C_WIDTH-1:0]    data_slave_w_strb_i;
    bit   [AXI_USER_WIDTH-1:0]        data_slave_w_user_i;
    bit                               data_slave_w_last_i;
    // used if ASYNC_INTF
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_w_writetoken_i;
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_w_readpointer_o;
    // used if !ASYNC_INTF
    bit                               data_slave_w_valid_i;
    bit                               data_slave_w_ready_o;

    // READ DATA CHANNEL
    bit   [AXI_DATA_S2C_WIDTH-1:0]    data_slave_r_data_o;
    bit   [1:0]                       data_slave_r_resp_o;
    bit                               data_slave_r_last_o;
    bit   [AXI_ID_IN_WIDTH-1:0]       data_slave_r_id_o;
    bit   [AXI_USER_WIDTH-1:0]        data_slave_r_user_o;
    // used if ASYNC_INTF
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_r_writetoken_o;
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_r_readpointer_i;
    // used if !ASYNC_INTF
    bit                               data_slave_r_valid_o;
    bit                               data_slave_r_ready_i;

    // WRITE RESPONSE CHANNEL
    bit   [1:0]                       data_slave_b_resp_o;
    bit   [AXI_ID_IN_WIDTH-1:0]       data_slave_b_id_o;
    bit   [AXI_USER_WIDTH-1:0]        data_slave_b_user_o;
    // used if ASYNC_INTF
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_b_writetoken_o;
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_slave_b_readpointer_i;
    // used if !ASYNC_INTF
    bit                               data_slave_b_valid_o;
    bit                               data_slave_b_ready_i;

    // AXI4 MASTER
    //***************************************
    // WRITE ADDRESS CHANNEL
    bit   [AXI_ADDR_WIDTH-1:0]        data_master_aw_addr_o;
    bit   [2:0]                       data_master_aw_prot_o;
    bit   [3:0]                       data_master_aw_region_o;
    bit   [7:0]                       data_master_aw_len_o;
    bit   [2:0]                       data_master_aw_size_o;
    bit   [1:0]                       data_master_aw_burst_o;
    bit                               data_master_aw_lock_o;
    bit   [5:0]                       data_master_aw_atop_o;
    bit   [3:0]                       data_master_aw_cache_o;
    bit   [3:0]                       data_master_aw_qos_o;
    bit   [AXI_ID_OUT_WIDTH-1:0]      data_master_aw_id_o;
    bit   [AXI_USER_WIDTH-1:0]        data_master_aw_user_o;
    // used if ASYNC_INTF
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_master_aw_writetoken_o;
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_master_aw_readpointer_i;
    // used if !ASYNC_INTF
    bit                               data_master_aw_valid_o;
    bit                               data_master_aw_ready_i;

    // READ ADDRESS CHANNEL
    bit   [AXI_ADDR_WIDTH-1:0]        data_master_ar_addr_o;
    bit   [2:0]                       data_master_ar_prot_o;
    bit   [3:0]                       data_master_ar_region_o;
    bit   [7:0]                       data_master_ar_len_o;
    bit   [2:0]                       data_master_ar_size_o;
    bit   [1:0]                       data_master_ar_burst_o;
    bit                               data_master_ar_lock_o;
    bit   [3:0]                       data_master_ar_cache_o;
    bit   [3:0]                       data_master_ar_qos_o;
    bit   [AXI_ID_OUT_WIDTH-1:0]      data_master_ar_id_o;
    bit   [AXI_USER_WIDTH-1:0]        data_master_ar_user_o;
    // used if ASYNC_INTF
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_master_ar_writetoken_o;
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_master_ar_readpointer_i;
    // used if !ASYNC_INTF
    bit                               data_master_ar_valid_o;
    bit                               data_master_ar_ready_i;

    // WRITE DATA CHANNEL
    bit   [AXI_DATA_C2S_WIDTH-1:0]    data_master_w_data_o;
    bit   [AXI_STRB_C2S_WIDTH-1:0]    data_master_w_strb_o;
    bit   [AXI_USER_WIDTH-1:0]        data_master_w_user_o;
    bit                               data_master_w_last_o;
    // used if ASYNC_INTF
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_master_w_writetoken_o;
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_master_w_readpointer_i;
    // used if !ASYNC_INTF
    bit                               data_master_w_valid_o;
    bit                               data_master_w_ready_i;

    // READ DATA CHANNEL
    bit   [AXI_DATA_C2S_WIDTH-1:0]    data_master_r_data_i;
    bit   [1:0]                       data_master_r_resp_i;
    bit                               data_master_r_last_i;
    bit   [AXI_ID_OUT_WIDTH-1:0]      data_master_r_id_i;
    bit   [AXI_USER_WIDTH-1:0]        data_master_r_user_i;
    // used if ASYNC_INTF
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_master_r_writetoken_i;
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_master_r_readpointer_o;
    // used if !ASYNC_INTF
    bit                               data_master_r_valid_i;
    bit                               data_master_r_ready_o;

    // WRITE RESPONSE CHANNEL
    bit   [1:0]                       data_master_b_resp_i;
    bit   [AXI_ID_OUT_WIDTH-1:0]      data_master_b_id_i;
    bit   [AXI_USER_WIDTH-1:0]        data_master_b_user_i;
    // used if ASYNC_INTF
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_master_b_writetoken_i;
    bit   [DC_SLICE_BUFFER_WIDTH-1:0] data_master_b_readpointer_o;
    // used if !ASYNC_INTF
    bit                               data_master_b_valid_i;
    bit                               data_master_b_ready_o;
    // ============================================================


    // ============================================================
    // instantiate dut
    // ============================================================
    pulp_cluster dut(.*);
    // ============================================================


    // ============================================================
    // AXI interface model
    // ============================================================
    // AXI-Master interface model
    // ============================================================
    axi4_mst_bfm #(
        .AXI_DATA_WIDTH ( AXI_DATA_S2C_WIDTH    ),
        .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH        )
    ) HOST (
        .clk            (clk_i                  ),
        .resetn         (rst_ni                 ),
        
        // axi4 master
        .araddr         (data_slave_ar_addr_i   ),
        .arburst        (data_slave_ar_burst_i  ),
        .arcache        (data_slave_ar_cache_i  ),
        .arlen          (data_slave_ar_len_i    ),
        .arlock         (data_slave_ar_lock_i   ),
        .arprot         (data_slave_ar_prot_i   ),
        .arqos          (data_slave_ar_qos_i    ),
        .arready        (data_slave_ar_ready_o  ),
        .arregion       (data_slave_ar_region_i ),
        .arsize         (data_slave_ar_size_i   ),
        .arvalid        (data_slave_ar_valid_i  ),
        
        .awaddr         (data_slave_aw_addr_i   ),
        .awburst        (data_slave_aw_burst_i  ),
        .awcache        (data_slave_aw_cache_i  ),
        .awlen          (data_slave_aw_len_i    ),
        .awlock         (data_slave_aw_lock_i   ),
        .awprot         (data_slave_aw_prot_i   ),
        .awqos          (data_slave_aw_qos_i    ),
        .awready        (data_slave_aw_ready_o  ),
        .awregion       (data_slave_aw_region_i ),
        .awsize         (data_slave_aw_size_i   ),
        .awvalid        (data_slave_aw_valid_i  ),
        
        .bready         (data_slave_b_ready_i   ),
        .bresp          (data_slave_b_resp_o    ),
        .bvalid         (data_slave_b_valid_o   ),
        
        .rdata          (data_slave_r_data_o    ),
        .rlast          (data_slave_r_last_o    ),
        .rready         (data_slave_r_ready_i   ),
        .rresp          (data_slave_r_resp_o    ),
        .rvalid         (data_slave_r_valid_o   ),
        
        .wdata          (data_slave_w_data_i    ),
        .wlast          (data_slave_w_last_i    ),
        .wready         (data_slave_w_ready_o   ),
        .wstrb          (data_slave_w_strb_i    ),
        .wvalid         (data_slave_w_valid_i   )
    );
    // ============================================================
    // AXI-Slave interface model(External Memory)
    // ============================================================
    AXI_MBIT_BUS_MODEL #(
        .DWIDTH      ( AXI_ADDR_WIDTH           ),   // Data-Width::Only valid 128 or 256
        .AWIDTH      ( AXI_DATA_C2S_WIDTH       ),   // Address-Width -- DO NOT CHANGE
        .IDWIDTH     ( AXI_ID_OUT_WIDTH         ),   // ID bit-Width
        .ACAPA       ( 16                       )    // Acceptance Capability
    ) EXT_MEMORY (
        .ACLK        (clk_i                     ),   // CLK for AXI
        .ARESETn     (rst_ni                    ),   // RESET
    
        .RD_BUS_HOLD ('0                        ),   // BRS control for read channel
        .WR_BUS_HOLD ('0                        ),   // BRS control for write channel
        .BR_BUS_HOLD ('0                        ),   // BRS control for back-response channel
    
        // AXI Read Address Ch
        .O_ARREADY   (data_master_ar_ready_i    ),   // Read address read
        .I_ARVALID   (data_master_ar_valid_o    ),   // Read address valid
        .I_ARID      (data_master_ar_id_o       ),   // Read address ID
        .I_ARADDR    (data_master_ar_addr_o     ),   // Read address
        .I_ARLEN     (data_master_ar_len_o      ),   // Burst length
        .I_ARBURST   (data_master_ar_burst_o    ),   // Burst type
    
        // AXI Read Data Ch
        .I_RREADY    (data_master_r_ready_o     ),   // Read data ready
        .O_RVALID    (data_master_r_valid_i     ),   // Read valid
        .O_RID       (data_master_r_id_i        ),   // Read data ID
        .O_RDATA     (data_master_r_data_i      ),   // Read data from AXI
        .O_RLAST     (data_master_r_last_i      ),   // Last read transfer
        .O_RRESP     (data_master_r_resp_i      ),   // Read status response - always okay in here.
    
        // AXI Write Address Ch
        .O_AWREADY   (data_master_aw_ready_i    ),   // Write address read
        .I_AWVALID   (data_master_aw_valid_o    ),   // Write address valid
        .I_AWID      (data_master_aw_id_o       ),   // Write address ID
        .I_AWADDR    (data_master_aw_addr_o     ),   // Write address
        .I_AWLEN     (data_master_aw_len_o      ),   // Burst length
        .I_AWBURST   (data_master_aw_burst_o    ),   // Burst type
    
        // AXI Write Data Ch
        .O_WREADY    (data_master_w_ready_i     ),   // Write data ready
        .I_WVALID    (data_master_w_valid_o     ),   // Write valid
        .I_WID       ('0                        ),   // Write data ID -- NOT USED
        .I_WSTRB     (data_master_w_strb_o      ),   // Write data strobe from AXI
        .I_WDATA     (data_master_w_data_o      ),   // Write data from AXI
        .I_WLAST     (data_master_w_last_o      ),   // Last read transfer
    
        // AXI Response Ch
        .I_BREADY    (data_master_b_ready_o     ),   // Write response READY
        .O_BVALID    (data_master_b_valid_i     ),   // Write response Valid
        .O_BRESP     (data_master_b_resp_i      ),   // Write response status
        .O_BID       (data_master_b_id_i        )    // Write response ID
    );
    // ============================================================


    // ============================================================
    // declare task
    // ============================================================
    `include "TB_TASK.sv"
    `include "DPI_TASK.sv"
    // ============================================================


endmodule
