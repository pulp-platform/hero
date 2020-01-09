// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


`timescale  1ns/1ps
`include "pulp_interfaces.sv"

module tb;

   parameter NB_CORES         = `NB_CORES;
   parameter AXI_DATA         = 64;
   parameter AXI_ADDR         = 32;
   parameter AXI_ID           = 7;
   parameter AXI_USER         = 4;

   parameter FETCH_ADDR_WIDTH = 32;
   parameter FETCH_DATA_WIDTH = 128;

   parameter PRI_NB_WAYS          = 4;
   parameter PRI_CACHE_SIZE       = 512;
   parameter PRI_CACHE_LINE       = 1;

   parameter SH_NB_BANKS         = `SH_NB_CACHE_BANKS;
   parameter SH_NB_WAYS          = 4;
   parameter SH_CACHE_SIZE       = 4*1024;
   parameter SH_CACHE_LINE       = 1;

   parameter L2_ADDR_WIDTH    = 20;
   parameter L2_SIZE          = 3*512*1024; // 1.5MB
   parameter USE_REDUCED_TAG  = "TRUE";

   parameter CLK_PERIOD       = 2.0;

   logic                                           clk;
   logic                                           rst_n;
   logic                                           test_en_i;

   logic [NB_CORES-1:0]                            fetch_enable;
   logic [NB_CORES-1:0][FETCH_DATA_WIDTH-1:0]      instr_r_rdata_L2_to_check;
   logic [AXI_ADDR-1:0]                            temp_address;

   logic [NB_CORES-1:0]                            eoc_int;

   event eoc_event;


   // signal from TGEN to hier icache
   logic [NB_CORES-1:0]                            fetch_req_int;
   logic [NB_CORES-1:0] [FETCH_ADDR_WIDTH-1:0]     fetch_addr_int;
   logic [NB_CORES-1:0]                            fetch_gnt_int;
   logic [NB_CORES-1:0]                            fetch_rvalid_int;
   logic [NB_CORES-1:0] [FETCH_DATA_WIDTH-1:0]     fetch_rdata_int;


   // Signals from icache_control_unit to Hier CAChe
   logic [NB_CORES-1:0]                            bypass_icache;
   logic [NB_CORES-1:0]                            cache_is_bypassed;
   logic [NB_CORES-1:0]                            flush_icache;
   logic [NB_CORES-1:0]                            cache_is_flushed;




   // Signal form cache to AXI mem IF
   logic [AXI_ID-1:0]               axi_master_arid_int;
   logic [AXI_ADDR-1:0]             axi_master_araddr_int;
   logic [7:0]                      axi_master_arlen_int;
   logic [2:0]                      axi_master_arsize_int;
   logic [1:0]                      axi_master_arburst_int;
   logic                            axi_master_arlock_int;
   logic [3:0]                      axi_master_arcache_int;
   logic [2:0]                      axi_master_arprot_int;
   logic [3:0]                      axi_master_arregion_int;
   logic [AXI_USER-1:0]             axi_master_aruser_int;
   logic [3:0]                      axi_master_arqos_int;
   logic                            axi_master_arvalid_int;
   logic                            axi_master_arready_int;

   logic [AXI_ID-1:0]               axi_master_rid_int;
   logic [AXI_DATA-1:0]             axi_master_rdata_int;
   logic [1:0]                      axi_master_rresp_int;
   logic                            axi_master_rlast_int;
   logic [AXI_USER-1:0]             axi_master_ruser_int;
   logic                            axi_master_rvalid_int;
   logic                            axi_master_rready_int;

   logic [AXI_ID-1:0]               axi_master_awid_int;
   logic [AXI_ADDR-1:0]             axi_master_awaddr_int;
   logic [7:0]                      axi_master_awlen_int;
   logic [2:0]                      axi_master_awsize_int;
   logic [1:0]                      axi_master_awburst_int;
   logic                            axi_master_awlock_int;
   logic [3:0]                      axi_master_awcache_int;
   logic [2:0]                      axi_master_awprot_int;
   logic [3:0]                      axi_master_awregion_int;
   logic [AXI_USER-1:0]             axi_master_awuser_int;
   logic [3:0]                      axi_master_awqos_int;
   logic                            axi_master_awvalid_int;
   logic                            axi_master_awready_int;

   logic  [AXI_DATA-1:0]            axi_master_wdata_int;
   logic  [AXI_DATA/8-1:0]          axi_master_wstrb_int;
   logic                            axi_master_wlast_int;
   logic  [ AXI_USER-1:0]           axi_master_wuser_int;
   logic                            axi_master_wvalid_int;
   logic                            axi_master_wready_int;

   logic  [AXI_ID-1:0]              axi_master_bid_int;
   logic  [ 1:0]                    axi_master_bresp_int;
   logic  [ AXI_USER-1:0]           axi_master_buser_int;
   logic                            axi_master_bvalid_int;
   logic                            axi_master_bready_int;

   logic                            mem_csn;
   logic                            mem_wen;
   logic [L2_ADDR_WIDTH-1:0]        mem_add;
   logic [63:0]                     mem_wdata;
   logic [7:0]                      mem_be;
   logic [63:0]                     mem_rdata;


   // Control ports for shared main cache banks
   SP_ICACHE_CTRL_UNIT_BUS      IC_ctrl_unit_bus_main[SH_NB_BANKS]();
   // Control ports for private cache banks
   PRI_ICACHE_CTRL_UNIT_BUS     IC_ctrl_unit_bus_pri[NB_CORES]();

   always @(posedge clk)
   begin
      if(eoc_int[0])
        -> eoc_event;
   end

   always
   begin
      #(CLK_PERIOD/2.0);
      clk <= ~clk;
   end


   logic [SH_NB_BANKS - 1 : 0] sh_clear_regs;
   logic [SH_NB_BANKS - 1 : 0] sh_enable_regs;
   logic [SH_NB_BANKS - 1 : 0] sh_req_enable;
   logic [SH_NB_BANKS - 1 : 0] sh_req_disable;
   logic [SH_NB_BANKS - 1 : 0] sh_flush_req;
   logic [SH_NB_BANKS - 1 : 0] sh_sel_flush_req;
   logic [SH_NB_BANKS - 1 : 0] [FETCH_ADDR_WIDTH - 1 : 0] sh_sel_flush_addr;

   logic [NB_CORES - 1 : 0] pri_bypass_req;
   logic [NB_CORES - 1 : 0] pri_flush_req;
   logic [NB_CORES - 1 : 0] pri_sel_flush_req;

   logic [NB_CORES - 1 : 0] enable_l1_l15_prefetch;
   logic                    special_core_icache;

   genvar   i;

   generate
      begin
         for(i=0;i<SH_NB_BANKS;i++)
           begin
              assign IC_ctrl_unit_bus_main[i].ctrl_clear_regs  = sh_clear_regs[i];
              assign IC_ctrl_unit_bus_main[i].ctrl_enable_regs = sh_enable_regs[i];
              assign IC_ctrl_unit_bus_main[i].ctrl_req_enable  = sh_req_enable[i];
              assign IC_ctrl_unit_bus_main[i].ctrl_req_disable = sh_req_disable[i];
              assign IC_ctrl_unit_bus_main[i].ctrl_flush_req   = sh_flush_req[i];
              assign IC_ctrl_unit_bus_main[i].sel_flush_req    = sh_sel_flush_req[i];
              assign IC_ctrl_unit_bus_main[i].sel_flush_addr   = sh_sel_flush_addr[i] ;
           end

         for(i=0;i<NB_CORES;i++)
           begin
              assign IC_ctrl_unit_bus_pri[i].bypass_req    = pri_bypass_req[i];
              assign IC_ctrl_unit_bus_pri[i].flush_req     = pri_flush_req[i];
              assign IC_ctrl_unit_bus_pri[i].sel_flush_req = pri_sel_flush_req[i];
           end

      end
   endgenerate

   initial
   begin
      clk          = '0;
      rst_n        = 1'b1;
      fetch_enable = '0;

      sh_clear_regs  = '0;
      sh_enable_regs = '0;

      pri_bypass_req    = '1;
      pri_flush_req     = '0;
      pri_sel_flush_req = '0;
      enable_l1_l15_prefetch = '0;
      special_core_icache = '0;

      sh_req_enable     = '0;
      sh_req_disable    = '1;
      sh_flush_req      = '0;
      sh_sel_flush_req  = '0;
      sh_sel_flush_addr = {'0, '0};

      @(negedge clk);
      @(negedge clk);

      rst_n = 1'b0;

      @(negedge clk);
      @(negedge clk);
      @(negedge clk);
      @(negedge clk);

      rst_n = 1'b1;
      @(negedge clk);
      @(negedge clk);
      @(negedge clk);
      @(negedge clk);
      @(negedge clk);

      // Start all COREs
      fetch_enable = '1;

      #1000;

      sh_req_disable    = 9'h000;
      sh_req_enable     = 9'h1FF;
      pri_bypass_req    = 9'h000;

      enable_l1_l15_prefetch = 9'h1FF;

      for(int i=0;i<100;i++)
        begin
           #4;
           enable_l1_l15_prefetch = 9'h000;
           #4;
           enable_l1_l15_prefetch = 9'h1FF;
        end

      @(eoc_event);

   end


   //////////////////////////////////////////
   // ████████╗ ██████╗ ███████╗███╗   ██╗ //
   // ╚══██╔══╝██╔════╝ ██╔════╝████╗  ██║ //
   //    ██║   ██║  ███╗█████╗  ██╔██╗ ██║ //
   //    ██║   ██║   ██║██╔══╝  ██║╚██╗██║ //
   //    ██║   ╚██████╔╝███████╗██║ ╚████║ //
   //    ╚═╝    ╚═════╝ ╚══════╝╚═╝  ╚═══╝ //
   //////////////////////////////////////////
   generate

      for(i=0;i<NB_CORES;i++)
      begin : CORE
         tgen_128
         #(
            .FETCH_ADDR_WIDTH (FETCH_ADDR_WIDTH),
            .FETCH_DATA_WIDTH (FETCH_DATA_WIDTH)
         )
         CORE
         (
            .clk            ( clk                  ),
            .rst_n          ( rst_n                ),

            .fetch_req_o    ( fetch_req_int[i]     ),
            .fetch_addr_o   ( fetch_addr_int[i]    ),
            .fetch_gnt_i    ( fetch_gnt_int[i]     ),
            .fetch_rvalid_i ( fetch_rvalid_int[i]  ),
            .fetch_rdata_i  ( fetch_rdata_int[i]   ),

            .fetch_enable_i ( fetch_enable[i]      ),
            .eoc_o          ( eoc_int[i]           )
         );

         // application code is loaded in this dummy L2_MEMORY
         ibus_lint_memory_128
         #(
            .addr_width      ( L2_ADDR_WIDTH                      )
         )
         L2_MEMORY_CHECK
         (
            .clk             ( clk                                  ),
            .rst_n           ( rst_n                                ),

            .lint_req_i      ( fetch_req_int[i] &  fetch_gnt_int[i] ),
            .lint_grant_o    (                                      ),
            .lint_addr_i     ( fetch_addr_int[i][L2_ADDR_WIDTH+3:4] ),

            .lint_r_rdata_o  ( instr_r_rdata_L2_to_check[i]         ),
            .lint_r_valid_o  (                                      )
         );


         // assertion to check fetch correctness
         always @(posedge clk)
         begin
            if(fetch_rvalid_int[i])
            begin
               if(fetch_rdata_int[i] !== instr_r_rdata_L2_to_check[i])
               begin
                  $error("Error on CORE FETCH INTERFACE[%d]: Expected %h, Got %h at time %t", i, instr_r_rdata_L2_to_check[i], fetch_rdata_int[i], $time );
                  $stop();
               end
            end
         end


      end
   endgenerate




   ////////////////////////////////////////////////////////////////////
   //  █████╗ ██╗  ██╗██╗        ██╗     ██████╗         ██╗███████╗ //
   // ██╔══██╗╚██╗██╔╝██║        ██║     ╚════██╗        ██║██╔════╝ //
   // ███████║ ╚███╔╝ ██║        ██║      █████╔╝        ██║█████╗   //
   // ██╔══██║ ██╔██╗ ██║        ██║     ██╔═══╝         ██║██╔══╝   //
   // ██║  ██║██╔╝ ██╗██║███████╗███████╗███████╗███████╗██║██║      //
   // ╚═╝  ╚═╝╚═╝  ╚═╝╚═╝╚══════╝╚══════╝╚══════╝╚══════╝╚═╝╚═╝      //
   ////////////////////////////////////////////////////////////////////
   axi_mem_if
   #(
       .AXI4_ADDRESS_WIDTH ( AXI_ADDR       ),
       .AXI4_RDATA_WIDTH   ( AXI_DATA       ),
       .AXI4_WDATA_WIDTH   ( AXI_DATA       ),
       .AXI4_ID_WIDTH      ( AXI_ID         ),
       .AXI4_USER_WIDTH    ( AXI_USER       ),
       .BUFF_DEPTH_SLAVE   ( 2              )
   )
   axi_mem_if_i
   (
       .ACLK               ( clk                     ),
       .ARESETn            ( rst_n                   ),
       .test_en_i          ( test_en_i               ),

       .AWVALID_i          ( axi_master_awvalid_int  ),
       .AWADDR_i           ( axi_master_awaddr_int   ),
       .AWPROT_i           ( axi_master_awprot_int   ),
       .AWREGION_i         ( axi_master_awregion_int ),
       .AWLEN_i            ( axi_master_awlen_int    ),
       .AWSIZE_i           ( axi_master_awsize_int   ),
       .AWBURST_i          ( axi_master_awburst_int  ),
       .AWLOCK_i           ( axi_master_awlock_int   ),
       .AWCACHE_i          ( axi_master_awcache_int  ),
       .AWQOS_i            ( axi_master_awqos_int    ),
       .AWID_i             ( axi_master_awid_int     ),
       .AWUSER_i           ( axi_master_awuser_int   ),
       .AWREADY_o          ( axi_master_awready_int  ),

       .ARVALID_i          ( axi_master_arvalid_int  ),
       .ARADDR_i           ( axi_master_araddr_int   ),
       .ARPROT_i           ( axi_master_arprot_int   ),
       .ARREGION_i         ( axi_master_arregion_int ),
       .ARLEN_i            ( axi_master_arlen_int    ),
       .ARSIZE_i           ( axi_master_arsize_int   ),
       .ARBURST_i          ( axi_master_arburst_int  ),
       .ARLOCK_i           ( axi_master_arlock_int   ),
       .ARCACHE_i          ( axi_master_arcache_int  ),
       .ARQOS_i            ( axi_master_arqos_int    ),
       .ARID_i             ( axi_master_arid_int     ),
       .ARUSER_i           ( axi_master_aruser_int   ),
       .ARREADY_o          ( axi_master_arready_int  ),

       .RVALID_o           ( axi_master_rvalid_int   ),
       .RDATA_o            ( axi_master_rdata_int    ),
       .RRESP_o            ( axi_master_rresp_int    ),
       .RLAST_o            ( axi_master_rlast_int    ),
       .RID_o              ( axi_master_rid_int      ),
       .RUSER_o            ( axi_master_ruser_int    ),
       .RREADY_i           ( axi_master_rready_int   ),

       .WVALID_i           ( axi_master_wvalid_int   ),
       .WDATA_i            ( axi_master_wdata_int    ),
       .WSTRB_i            ( axi_master_wstrb_int    ),
       .WLAST_i            ( axi_master_wlast_int    ),
       .WUSER_i            ( axi_master_wuser_int    ),
       .WREADY_o           ( axi_master_wready_int   ),

       .BVALID_o           ( axi_master_bvalid_int   ),
       .BRESP_o            ( axi_master_bresp_int    ),
       .BID_o              ( axi_master_bid_int      ),
       .BUSER_o            ( axi_master_buser_int    ),
       .BREADY_i           ( axi_master_bready_int   ),

       .CEN                ( mem_csn                 ),
       .WEN                ( mem_wen                 ),
       .A                  ( temp_address            ),
       .D                  ( mem_wdata               ),
       .BE                 ( mem_be                  ),
       .Q                  ( mem_rdata               )
   );

   assign mem_add = temp_address[L2_ADDR_WIDTH+2:3];

   l2_generic
   #(
      .ADDR_WIDTH (L2_ADDR_WIDTH)
   )
   l2_mem_i
   (
      .CLK   ( clk          ),
      .RSTN  ( rst_n        ),
      .D     ( mem_wdata    ),
      .A     ( mem_add      ),
      .CEN   ( mem_csn      ),
      .WEN   ( mem_wen      ),
      .BE    ( mem_be       ),
      .Q     ( mem_rdata    )
   );

   ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // ███╗   ███╗ █████╗ ██╗███╗   ██╗    ██╗███╗   ██╗███████╗████████╗     ██████╗ █████╗  ██████╗██╗  ██╗███████╗ //
   // ████╗ ████║██╔══██╗██║████╗  ██║    ██║████╗  ██║██╔════╝╚══██╔══╝    ██╔════╝██╔══██╗██╔════╝██║  ██║██╔════╝ //
   // ██╔████╔██║███████║██║██╔██╗ ██║    ██║██╔██╗ ██║███████╗   ██║       ██║     ███████║██║     ███████║█████╗   //
   // ██║╚██╔╝██║██╔══██║██║██║╚██╗██║    ██║██║╚██╗██║╚════██║   ██║       ██║     ██╔══██║██║     ██╔══██║██╔══╝   //
   // ██║ ╚═╝ ██║██║  ██║██║██║ ╚████║    ██║██║ ╚████║███████║   ██║       ╚██████╗██║  ██║╚██████╗██║  ██║███████╗ //
   // ╚═╝     ╚═╝╚═╝  ╚═╝╚═╝╚═╝  ╚═══╝    ╚═╝╚═╝  ╚═══╝╚══════╝   ╚═╝        ╚═════╝╚═╝  ╚═╝ ╚═════╝╚═╝  ╚═╝╚══════╝ //
   ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   icache_hier_top
   #(
      .FETCH_ADDR_WIDTH  ( FETCH_ADDR_WIDTH ), // 32,
      .FETCH_DATA_WIDTH  ( FETCH_DATA_WIDTH ), // 128,

      .NB_CORES          ( NB_CORES         ), // 8,


      .SH_NB_BANKS       ( SH_NB_BANKS      ), // 2,
      .SH_NB_WAYS        ( SH_NB_WAYS       ), // 4,
      .SH_CACHE_SIZE     ( SH_CACHE_SIZE    ), // 32*1024, // in Byte
      .SH_CACHE_LINE     ( SH_CACHE_LINE    ), // 1,       // in word of [FETCH_DATA_WIDTH]

      .PRI_NB_WAYS       ( PRI_NB_WAYS      ), // 4,
      .PRI_CACHE_SIZE    ( PRI_CACHE_SIZE   ), // 256, // in Byte
      .PRI_CACHE_LINE    ( PRI_CACHE_LINE   ), // 1,   // in word of [FETCH_DATA_WIDTH]

      .USE_SPECIAL_CORE       ( "TRUE"     ),
      .SPECIAL_CORE_ID        ( 8          ),
      .SPECIAL_PRI_CACHE_SIZE ( 1024       ), // 1024 in Byte

      .AXI_ID            ( AXI_ID           ), // 6,
      .AXI_ADDR          ( AXI_ADDR         ), // 32,
      .AXI_USER          ( AXI_USER         ), // 6,
      .AXI_DATA          ( AXI_DATA         ), // 64,

      .USE_REDUCED_TAG   ( USE_REDUCED_TAG  ), // "TRUE",   // TRUE | FALSE
      .L2_SIZE           ( L2_SIZE          )  // 512*1024    // Size of max(L2 ,ROM) program memory in Byte
   )
   DUT
   (
      .clk                     ( clk                       ),  // input logic
      .rst_n                   ( rst_n                     ),  // input logic
      .test_en_i               ( test_en_i                 ),  // input logic

      // interface with processors
      .fetch_req_i             ( fetch_req_int             ),  // input  logic [NB_CORES-1:0]
      .fetch_addr_i            ( fetch_addr_int            ),  // input  logic [NB_CORES-1:0][FETCH_ADDR_WIDTH-1:0]
      .fetch_gnt_o             ( fetch_gnt_int             ),  // output logic [NB_CORES-1:0]
      .fetch_rvalid_o          ( fetch_rvalid_int          ),  // output logic [NB_CORES-1:0]
      .fetch_rdata_o           ( fetch_rdata_int           ),  // output logic [NB_CORES-1:0][FETCH_DATA_WIDTH-1:0]


      //AXI read address bus -------------------------------------------
      .axi_master_arid_o       ( axi_master_arid_int      ),  // output  logic [AXI_ID-1:0]
      .axi_master_araddr_o     ( axi_master_araddr_int    ),  // output  logic [AXI_ADDR-1:0]
      .axi_master_arlen_o      ( axi_master_arlen_int     ),  // output  logic [ 7:0]
      .axi_master_arsize_o     ( axi_master_arsize_int    ),  // output  logic [ 2:0]
      .axi_master_arburst_o    ( axi_master_arburst_int   ),  // output  logic [ 1:0]
      .axi_master_arlock_o     ( axi_master_arlock_int    ),  // output  logic
      .axi_master_arcache_o    ( axi_master_arcache_int   ),  // output  logic [ 3:0]
      .axi_master_arprot_o     ( axi_master_arprot_int    ),  // output  logic [ 2:0]
      .axi_master_arregion_o   ( axi_master_arregion_int  ),  // output  logic [ 3:0]
      .axi_master_aruser_o     ( axi_master_aruser_int    ),  // output  logic [ AXI_USER-1:0]
      .axi_master_arqos_o      ( axi_master_arqos_int     ),  // output  logic [ 3:0]
      .axi_master_arvalid_o    ( axi_master_arvalid_int   ),  // output  logic
      .axi_master_arready_i    ( axi_master_arready_int   ),  // input logic
      // --------------------------------------------------------------


      //AXI BACKWARD read data bus ---------------------------------------------
      .axi_master_rid_i        ( axi_master_rid_int       ),  // input   logic [AXI_ID-1:0]
      .axi_master_rdata_i      ( axi_master_rdata_int     ),  // input   logic [AXI_DATA-1:0]
      .axi_master_rresp_i      ( axi_master_rresp_int     ),  // input   logic [1:0]
      .axi_master_rlast_i      ( axi_master_rlast_int     ),  // input   logic
      .axi_master_ruser_i      ( axi_master_ruser_int     ),  // input   logic [AXI_USER-1:0]
      .axi_master_rvalid_i     ( axi_master_rvalid_int    ),  // input   logic
      .axi_master_rready_o     ( axi_master_rready_int    ),  // output  logic

      // NOT USED ----------------------------------------------
      .axi_master_awid_o       ( axi_master_awid_int      ),  // output logic [AXI_ID-1:0]
      .axi_master_awaddr_o     ( axi_master_awaddr_int    ),  // output logic [AXI_ADDR-1:0]
      .axi_master_awlen_o      ( axi_master_awlen_int     ),  // output logic [ 7:0]
      .axi_master_awsize_o     ( axi_master_awsize_int    ),  // output logic [ 2:0]
      .axi_master_awburst_o    ( axi_master_awburst_int   ),  // output logic [ 1:0]
      .axi_master_awlock_o     ( axi_master_awlock_int    ),  // output logic
      .axi_master_awcache_o    ( axi_master_awcache_int   ),  // output logic [ 3:0]
      .axi_master_awprot_o     ( axi_master_awprot_int    ),  // output logic [ 2:0]
      .axi_master_awregion_o   ( axi_master_awregion_int  ),  // output logic [ 3:0]
      .axi_master_awuser_o     ( axi_master_awuser_int    ),  // output logic [ AXI_USER-1:0]
      .axi_master_awqos_o      ( axi_master_awqos_int     ),  // output logic [ 3:0]
      .axi_master_awvalid_o    ( axi_master_awvalid_int   ),  // output logic
      .axi_master_awready_i    ( axi_master_awready_int   ),  // input  logic

      // NOT USED ----------------------------------------------
      .axi_master_wdata_o      ( axi_master_wdata_int      ),  // output logic  [AXI_DATA-1:0]
      .axi_master_wstrb_o      ( axi_master_wstrb_int      ),  // output logic  [AXI_DATA/8-1:0]
      .axi_master_wlast_o      ( axi_master_wlast_int      ),  // output logic
      .axi_master_wuser_o      ( axi_master_wuser_int      ),  // output logic  [ AXI_USER-1:0]
      .axi_master_wvalid_o     ( axi_master_wvalid_int     ),  // output logic
      .axi_master_wready_i     ( axi_master_wready_int     ),  // input  logic
      // ---------------------------------------------------------------

      // NOT USED ----------------------------------------------
      .axi_master_bid_i        ( axi_master_bid_int        ),  // input  logic  [AXI_ID-1:0]
      .axi_master_bresp_i      ( axi_master_bresp_int      ),  // input  logic  [ 1:0]
      .axi_master_buser_i      ( axi_master_buser_int      ),  // input  logic  [ AXI_USER-1:0]
      .axi_master_bvalid_i     ( axi_master_bvalid_int     ),  // input  logic
      .axi_master_bready_o     ( axi_master_bready_int     ),  // output logic
      // ---------------------------------------------------------------
       .enable_l1_l15_prefetch_i ( enable_l1_l15_prefetch   ),
       .special_core_dest_i    ( special_core_icache        ),

       .IC_ctrl_unit_bus_pri   ( IC_ctrl_unit_bus_pri      ),
       .IC_ctrl_unit_bus_main  ( IC_ctrl_unit_bus_main     )
   );
endmodule
