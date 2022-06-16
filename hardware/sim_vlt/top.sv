`include "axi/assign.svh"
`include "axi/typedef.svh"

module top;
    import pulp_cluster_package::*; 
    import apu_package::*; 
    import apu_core_package::*;


    // ============================================================
    // declare dut parameter
    // ============================================================
    // cluster parameters
    parameter bit ASYNC_INTF          = 1'b1;     // RV-CORE is on async-clock domain
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
    bit                               clk_i;
    bit                               rst_ni;
    bit                               ref_clk_i;
    bit                               pmu_mem_pwdn_i;

    bit   [3:0]                        base_addr_i;

    bit                                test_mode_i;

    bit                                en_sa_boot_i;

    bit   [5:0]                        cluster_id_i;

    bit                                fetch_en_i;

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
    // generate clock & reset
    // ============================================================
    localparam real freq            = 800.0; // 800MHz
    localparam real clk_period      = 1000.0/freq;
    localparam real clk_period_div2 = 500.0/freq;
    initial begin
        $display("clk_period_div is %f", clk_period_div2);
        forever begin
            $display("here, in clk");
            #1
            clk_i = ~clk_i;
        end
    end

//    `define wait_for(signal) \
//      do \
//        @(posedge clk_i); \
//      while (!signal);
    // ============================================================


//    // ============================================================
//    // External Memory model
//    // ============================================================
//    AXI_BUS #(
//        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH         ),
//        .AXI_DATA_WIDTH (AXI_DATA_C2S_WIDTH     ),
//        .AXI_ID_WIDTH   (AXI_ID_OUT_WIDTH+1     ),
//        .AXI_USER_WIDTH (AXI_USER_WIDTH         )
//    ) axi_sim_mem_bus();
//
//    // Emulate infinite memory with AXI slave port.
//    axi_sim_mem_intf #(
//        .AddrWidth          (AXI_ADDR_WIDTH       ),
//        .DataWidth          (AXI_DATA_C2S_WIDTH   ),
//        .IdWidth            (AXI_ID_OUT_WIDTH+1   ),
//        .UserWidth          (AXI_USER_WIDTH       ),
//        .WarnUninitialized  (1'b0                 ),
//        .ApplDelay          (clk_period / 5 * 1),
//        .AcqDelay           (clk_period / 5 * 4)
//    ) i_sim_mem (
//        .clk_i    (clk_i          ),
//        .rst_ni   (rst_ni         ),
//        .axi_slv  (axi_sim_mem_bus)
//    );
//    // ============================================================
//    // binding axi_sim_mem_bus interface
//    always_comb begin:binding_axi_sim_mem_bus
//        axi_sim_mem_bus.aw_valid   = data_master_aw_valid_o     ;
//        axi_sim_mem_bus.aw_addr    = data_master_aw_addr_o      ;
//        axi_sim_mem_bus.aw_prot    = data_master_aw_prot_o      ;
//        axi_sim_mem_bus.aw_region  = data_master_aw_region_o    ;
//        axi_sim_mem_bus.aw_len     = data_master_aw_len_o       ;
//        axi_sim_mem_bus.aw_size    = data_master_aw_size_o      ;
//        axi_sim_mem_bus.aw_burst   = data_master_aw_burst_o     ;
//        axi_sim_mem_bus.aw_lock    = data_master_aw_lock_o      ;
//        axi_sim_mem_bus.aw_atop    = data_master_aw_atop_o      ;
//        axi_sim_mem_bus.aw_cache   = data_master_aw_cache_o     ;
//        axi_sim_mem_bus.aw_qos     = data_master_aw_qos_o       ;
//        axi_sim_mem_bus.aw_id      = data_master_aw_id_o        ;
//        axi_sim_mem_bus.aw_user    = data_master_aw_user_o      ;
//        data_master_aw_ready_i     = axi_sim_mem_bus.aw_ready   ;
//
//        axi_sim_mem_bus.ar_valid   = data_master_ar_valid_o     ;
//        axi_sim_mem_bus.ar_addr    = data_master_ar_addr_o      ;
//        axi_sim_mem_bus.ar_prot    = data_master_ar_prot_o      ;
//        axi_sim_mem_bus.ar_region  = data_master_ar_region_o    ;
//        axi_sim_mem_bus.ar_len     = data_master_ar_len_o       ;
//        axi_sim_mem_bus.ar_size    = data_master_ar_size_o      ;
//        axi_sim_mem_bus.ar_burst   = data_master_ar_burst_o     ;
//        axi_sim_mem_bus.ar_lock    = data_master_ar_lock_o      ;
//        axi_sim_mem_bus.ar_cache   = data_master_ar_cache_o     ;
//        axi_sim_mem_bus.ar_qos     = data_master_ar_qos_o       ;
//        axi_sim_mem_bus.ar_id      = data_master_ar_id_o        ;
//        axi_sim_mem_bus.ar_user    = data_master_ar_user_o      ;
//        data_master_ar_ready_i     = axi_sim_mem_bus.ar_ready   ;
//
//        axi_sim_mem_bus.w_valid    = data_master_w_valid_o      ;
//        axi_sim_mem_bus.w_data     = data_master_w_data_o       ;
//        axi_sim_mem_bus.w_strb     = data_master_w_strb_o       ;
//        axi_sim_mem_bus.w_user     = data_master_w_user_o       ;
//        axi_sim_mem_bus.w_last     = data_master_w_last_o       ;
//        data_master_w_ready_i      = axi_sim_mem_bus.w_ready    ;
//
//        data_master_r_valid_i      = axi_sim_mem_bus.r_valid    ;
//        data_master_r_data_i       = axi_sim_mem_bus.r_data     ;
//        data_master_r_resp_i       = axi_sim_mem_bus.r_resp     ;
//        data_master_r_last_i       = axi_sim_mem_bus.r_last     ;
//        data_master_r_id_i         = axi_sim_mem_bus.r_id       ;
//        data_master_r_user_i       = axi_sim_mem_bus.r_user     ;
//        axi_sim_mem_bus.r_ready    = data_master_r_ready_o      ;
//
//        data_master_b_valid_i      = axi_sim_mem_bus.b_valid    ;
//        data_master_b_resp_i       = axi_sim_mem_bus.b_resp     ;
//        data_master_b_id_i         = axi_sim_mem_bus.b_id       ;
//        data_master_b_user_i       = axi_sim_mem_bus.b_user     ;
//        axi_sim_mem_bus.b_ready    = data_master_b_ready_o      ;
//    end:binding_axi_sim_mem_bus
//    // ============================================================
//
//    // ============================================================
//    // TB-TASK
//    // ============================================================
//    task dut_init;
//        $display("dut init");
//        rst_ni = 0;
//        #100ns
//        rst_ni = 1;
//    endtask:dut_init
//
//    task write_to_klas(
//        input [AXI_ADDR_WIDTH-1:0] addr, 
//        input [AXI_DATA_S2C_WIDTH-1:0] data, 
//        output [1:0] resp
//    );
//        data_slave_aw_id_i = '0;
//        data_slave_aw_addr_i = addr;
//        data_slave_aw_len_i = '0;
//        data_slave_aw_size_i = $clog2(AXI_DATA_S2C_WIDTH/8);
//        data_slave_aw_burst_i = axi_pkg::BURST_INCR;
//        data_slave_aw_lock_i = 1'b0;
//        data_slave_aw_cache_i = '0;
//        data_slave_aw_prot_i = '0;
//        data_slave_aw_qos_i = '0;
//        data_slave_aw_region_i = '0;
//        data_slave_aw_atop_i = '0;
//        data_slave_aw_user_i = '0;
//        data_slave_aw_valid_i = 1'b1;
//        `wait_for(data_slave_aw_ready_o)
//        data_slave_aw_valid_i = 1'b0;
//        data_slave_w_data_i = data;
//        data_slave_w_strb_i = '1;
//        data_slave_w_last_i = 1'b1;
//        data_slave_w_user_i = '0;
//        data_slave_w_valid_i = 1'b1;
//        `wait_for(data_slave_w_ready_o)
//        data_slave_w_valid_i = 1'b0;
//        data_slave_b_ready_i = 1'b1;
//        `wait_for(data_slave_b_valid_o)
//        resp = data_slave_b_resp_o;
//        data_slave_b_ready_i = 1'b0;
//    endtask:write_to_klas
//
//    task read_from_klas(
//        input [AXI_ADDR_WIDTH-1:0] addr, 
//        output [AXI_DATA_S2C_WIDTH-1:0] data, 
//        output [1:0] resp
//    );
//        data_slave_ar_id_i = '0;
//        data_slave_ar_addr_i = addr;
//        data_slave_ar_len_i = '0;
//        data_slave_ar_size_i = $clog2(AXI_DATA_S2C_WIDTH/8);
//        data_slave_ar_burst_i = axi_pkg::BURST_INCR;
//        data_slave_ar_lock_i = 1'b0;
//        data_slave_ar_cache_i = '0;
//        data_slave_ar_prot_i = '0;
//        data_slave_ar_qos_i = '0;
//        data_slave_ar_region_i = '0;
//        data_slave_ar_user_i = '0;
//        data_slave_ar_valid_i = 1'b1;
//        `wait_for(data_slave_ar_ready_o)
//        data_slave_ar_valid_i = 1'b0;
//        data_slave_r_ready_i = 1'b1;
//        `wait_for(data_slave_r_valid_o)
//        data = data_slave_r_data_o;
//        resp = data_slave_r_resp_o;
//        data_slave_r_ready_i = 1'b0;
//    endtask:read_from_klas
//    // ============================================================
//
//
//    // ============================================================
//    // simple test
//    // ============================================================
//    bit     [AXI_DATA_S2C_WIDTH-1:0]    s2c_data;
//    bit     [1:0]                       s2c_resp;
//    bit     [AXI_DATA_C2S_WIDTH-1:0]    c2s_data;
//    bit     [1:0]                       c2s_resp;
//    initial begin
//        dut_init;
//        s2c_data  = 'h900dc00d;
//        write_to_klas('h1000_0000, s2c_data, s2c_resp);
//        s2c_data  = '0;
//        read_from_klas('h1000_0000, s2c_data, s2c_resp);
//        $display("s2c_data is %h", s2c_data);
//        $display("s2c_data is %h", s2c_resp);
//        #100
//        $finish;
//    end
//    // ============================================================


endmodule
