////////////////////////////////////////////////////////////////////////////////
// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

//                                                                            //
// Company:        Micrel Lab @ DEIS - University of Bologna                  //
//                    Viale Risorgimento 2 40136                              //
//                    Bologna - fax 0512093785 -                              //
//                                                                            //
// Engineer:       Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    20/10/2019                                                 //
// Design Name:    ICACHE EXPL                                                //
// Module Name:    icache_hier_top                                            //
// Project Name:   PULP                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    This block represents the top module for the shared cache  //
//                 It instanciates the master cache controller, the TAG/DATA  //
//                 array and the HW prefetcher.                               //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 23/01/2018 : File Created                                  //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`define FEATURE_ICACHE_STAT

module icache_hier_top
#(
   parameter FETCH_ADDR_WIDTH  = 32,
   parameter FETCH_DATA_WIDTH  = 128,

   parameter NB_CORES          = 9,

   parameter SH_NB_BANKS       = 2,
   parameter SH_NB_WAYS        = 4,
   parameter SH_CACHE_SIZE     = 4*1024, // in Byte
   parameter SH_CACHE_LINE     = 1,       // in word of [FETCH_DATA_WIDTH]

   parameter PRI_NB_WAYS       = 2,
   parameter PRI_CACHE_SIZE    = 512,       // in Byte
   parameter PRI_CACHE_LINE    = 1,         // in word of [FETCH_DATA_WIDTH]

   parameter AXI_ID            = 6,
   parameter AXI_ADDR          = 32,
   parameter AXI_USER          = 6,
   parameter AXI_DATA          = 64,

   parameter USE_REDUCED_TAG   = "TRUE",   // TRUE | FALSE
   parameter L2_SIZE           = 512*1024    // Size of max(L2 ,ROM) program memory in Byte
)
(
   input logic                                          clk,
   input logic                                          rst_n,
   input logic                                          test_en_i,

   // DFT ports (no suffixes due to partner request)
   input logic [25:0]                                   mem_ctrl,
   input logic                                          dft_ram_gt_se,
   input logic                                          dft_ram_bypass,
   input logic                                          dft_ram_bp_clk_en,

   // interface with processors
   input  logic [NB_CORES-1:0]                          fetch_req_i,
   input  logic [NB_CORES-1:0][FETCH_ADDR_WIDTH-1:0]    fetch_addr_i,
   output logic [NB_CORES-1:0]                          fetch_gnt_o,

   output logic [NB_CORES-1:0]                          fetch_rvalid_o,
   output logic [NB_CORES-1:0][FETCH_DATA_WIDTH-1:0]    fetch_rdata_o,



   //AXI read address bus -------------------------------------------
   output  logic [AXI_ID-1:0]                           axi_master_arid_o,
   output  logic [AXI_ADDR-1:0]                         axi_master_araddr_o,
   output  logic [ 7:0]                                 axi_master_arlen_o,    //burst length - 1 to 16
   output  logic [ 2:0]                                 axi_master_arsize_o,   //size of each transfer in burst
   output  logic [ 1:0]                                 axi_master_arburst_o,  //for bursts>1, accept only incr burst=01
   output  logic                                        axi_master_arlock_o,   //only normal access supported axs_awlock=00
   output  logic [ 3:0]                                 axi_master_arcache_o,
   output  logic [ 2:0]                                 axi_master_arprot_o,
   output  logic [ 3:0]                                 axi_master_arregion_o, //
   output  logic [ AXI_USER-1:0]                        axi_master_aruser_o,   //
   output  logic [ 3:0]                                 axi_master_arqos_o,    //
   output  logic                                        axi_master_arvalid_o,  //master addr valid
   input logic                                          axi_master_arready_i,  //slave ready to accept
   // --------------------------------------------------------------


   //AXI BACKWARD read data bus ---------------------------------------------
   input   logic [AXI_ID-1:0]                           axi_master_rid_i,
   input   logic [AXI_DATA-1:0]                         axi_master_rdata_i,
   input   logic [1:0]                                  axi_master_rresp_i,
   input   logic                                        axi_master_rlast_i,    //last transfer in burst
   input   logic [AXI_USER-1:0]                         axi_master_ruser_i,
   input   logic                                        axi_master_rvalid_i,   //slave data valid
   output  logic                                        axi_master_rready_o,    //master ready to accept

   // NOT USED ----------------------------------------------
   output logic [AXI_ID-1:0]                            axi_master_awid_o,
   output logic [AXI_ADDR-1:0]                          axi_master_awaddr_o,
   output logic [ 7:0]                                  axi_master_awlen_o,
   output logic [ 2:0]                                  axi_master_awsize_o,
   output logic [ 1:0]                                  axi_master_awburst_o,
   output logic                                         axi_master_awlock_o,
   output logic [ 3:0]                                  axi_master_awcache_o,
   output logic [ 2:0]                                  axi_master_awprot_o,
   output logic [ 3:0]                                  axi_master_awregion_o,
   output logic [ AXI_USER-1:0]                         axi_master_awuser_o,
   output logic [ 3:0]                                  axi_master_awqos_o,
   output logic                                         axi_master_awvalid_o,
   input  logic                                         axi_master_awready_i,

   // NOT USED ----------------------------------------------
   output logic  [AXI_DATA-1:0]                         axi_master_wdata_o,
   output logic  [AXI_DATA/8-1:0]                       axi_master_wstrb_o,
   output logic                                         axi_master_wlast_o,
   output logic  [ AXI_USER-1:0]                        axi_master_wuser_o,
   output logic                                         axi_master_wvalid_o,
   input  logic                                         axi_master_wready_i,
   // ---------------------------------------------------------------

   // NOT USED ----------------------------------------------
   input  logic  [AXI_ID-1:0]                           axi_master_bid_i,
   input  logic  [ 1:0]                                 axi_master_bresp_i,
   input  logic  [ AXI_USER-1:0]                        axi_master_buser_i,
   input  logic                                         axi_master_bvalid_i,
   output logic                                         axi_master_bready_o,
   // ---------------------------------------------------------------

   input  logic [NB_CORES-1:0]                          enable_l1_l15_prefetch_i,

   SP_ICACHE_CTRL_UNIT_BUS.Slave                        IC_ctrl_unit_bus_main[SH_NB_BANKS],
   PRI_ICACHE_CTRL_UNIT_BUS.Slave                       IC_ctrl_unit_bus_pri[NB_CORES]
);

   // signals from PRI cache and interconnect
   logic [2*NB_CORES-1:0]                                 refill_req_int;
   logic [2*NB_CORES-1:0]                                 refill_gnt_int;
   logic [2*NB_CORES-1:0] [FETCH_ADDR_WIDTH-1:0]          refill_addr_int;
   logic [2*NB_CORES-1:0]                                 refill_r_valid_int;
   logic [2*NB_CORES-1:0] [FETCH_DATA_WIDTH-1:0]          refill_r_data_int;

   // to LINT2AXI
   logic                                                refill_to_AXINODE_req_int;
   logic                                                refill_to_AXINODE_gnt_int;
   logic  [FETCH_ADDR_WIDTH-1:0]                        refill_to_AXINODE_addr_int;
   logic                                                refill_to_AXINODE_r_valid_int;
   logic  [FETCH_DATA_WIDTH-1:0]                        refill_to_AXINODE_r_data_int;




   // signal from icache-int to main icache
   logic [SH_NB_BANKS-1:0]                              fetch_req_to_main_cache;
   logic [SH_NB_BANKS-1:0][FETCH_ADDR_WIDTH-1:0]        fetch_addr_to_main_cache;
   logic [SH_NB_BANKS-1:0][2*NB_CORES-1:0]              fetch_ID_to_main_cache;
   logic [SH_NB_BANKS-1:0]                              fetch_gnt_from_main_cache;
   logic [SH_NB_BANKS-1:0][FETCH_DATA_WIDTH-1:0]        fetch_rdata_from_main_cache;
   logic [SH_NB_BANKS-1:0]                              fetch_rvalid_from_to_main_cache;
   logic [SH_NB_BANKS-1:0][2*NB_CORES-1:0]              fetch_rID_from_main_cache;

   // signal from icache-sh banks to axi node
   localparam  AXI_ID_INT  =  1;
   localparam  AXI_ID_OUT  =  $clog2(SH_NB_BANKS) + AXI_ID_INT;
   localparam  ADDR_OFFSET =  $clog2(FETCH_DATA_WIDTH)-3;

   logic [SH_NB_BANKS-1:0][AXI_ID_INT-1:0]             axi_master_awid_int;
   logic [SH_NB_BANKS-1:0][AXI_ADDR-1:0]               axi_master_awaddr_int;
   logic [SH_NB_BANKS-1:0][ 7:0]                       axi_master_awlen_int;
   logic [SH_NB_BANKS-1:0][ 2:0]                       axi_master_awsize_int;
   logic [SH_NB_BANKS-1:0][ 1:0]                       axi_master_awburst_int;
   logic [SH_NB_BANKS-1:0]                             axi_master_awlock_int;
   logic [SH_NB_BANKS-1:0][ 3:0]                       axi_master_awcache_int;
   logic [SH_NB_BANKS-1:0][ 2:0]                       axi_master_awprot_int;
   logic [SH_NB_BANKS-1:0][ 3:0]                       axi_master_awregion_int;
   logic [SH_NB_BANKS-1:0][ AXI_USER-1:0]              axi_master_awuser_int;
   logic [SH_NB_BANKS-1:0][ 3:0]                       axi_master_awqos_int;
   logic [SH_NB_BANKS-1:0]                             axi_master_awvalid_int;
   logic [SH_NB_BANKS-1:0]                             axi_master_awready_int;

    //AXI write data bus -------------- // // --------------
   logic [SH_NB_BANKS-1:0] [AXI_DATA-1:0]              axi_master_wdata_int;
   logic [SH_NB_BANKS-1:0] [AXI_DATA/8-1:0]            axi_master_wstrb_int;
   logic [SH_NB_BANKS-1:0]                             axi_master_wlast_int;
   logic [SH_NB_BANKS-1:0] [ AXI_USER-1:0]             axi_master_wuser_int;
   logic [SH_NB_BANKS-1:0]                             axi_master_wvalid_int;
   logic [SH_NB_BANKS-1:0]                             axi_master_wready_int;
    // ---------------------------------------------------------------

    //AXI BACKWARD write response bus -------------- // // --------------
   logic [SH_NB_BANKS-1:0] [AXI_ID_INT-1:0]            axi_master_bid_int;
   logic [SH_NB_BANKS-1:0] [ 1:0]                      axi_master_bresp_int;
   logic [SH_NB_BANKS-1:0] [ AXI_USER-1:0]             axi_master_buser_int;
   logic [SH_NB_BANKS-1:0]                             axi_master_bvalid_int;
   logic [SH_NB_BANKS-1:0]                             axi_master_bready_int;
    // ---------------------------------------------------------------

    //AXI read address bus -------------------------------------------
   logic [SH_NB_BANKS-1:0][AXI_ID_INT-1:0]             axi_master_arid_int;       //
   logic [SH_NB_BANKS-1:0][AXI_ADDR-1:0]               axi_master_araddr_int;     //
   logic [SH_NB_BANKS-1:0][ 7:0]                       axi_master_arlen_int;      // burst length - 1 to 256
   logic [SH_NB_BANKS-1:0][ 2:0]                       axi_master_arsize_int;     // size of each transfer in burst
   logic [SH_NB_BANKS-1:0][ 1:0]                       axi_master_arburst_int;    // for bursts>1, accept only incr burst=01
   logic [SH_NB_BANKS-1:0]                             axi_master_arlock_int;     // only normal access supported axs_awlock=00
   logic [SH_NB_BANKS-1:0][ 3:0]                       axi_master_arcache_int;    //
   logic [SH_NB_BANKS-1:0][ 2:0]                       axi_master_arprot_int;     //
   logic [SH_NB_BANKS-1:0][ 3:0]                       axi_master_arregion_int;   //
   logic [SH_NB_BANKS-1:0][ AXI_USER-1:0]              axi_master_aruser_int;     //
   logic [SH_NB_BANKS-1:0][ 3:0]                       axi_master_arqos_int;      //
   logic [SH_NB_BANKS-1:0]                             axi_master_arvalid_int;    // master addr valid
   logic [SH_NB_BANKS-1:0]                             axi_master_arready_int;    // slave ready to accept
    // --------------------------------------------------------------------------------

    //AXI BACKWARD read data bus ----------------------------------------------
   logic [SH_NB_BANKS-1:0][AXI_ID_INT-1:0]             axi_master_rid_int;        //
   logic [SH_NB_BANKS-1:0][AXI_DATA-1:0]               axi_master_rdata_int;      //
   logic [SH_NB_BANKS-1:0][ 1:0]                       axi_master_rresp_int;      //
   logic [SH_NB_BANKS-1:0]                             axi_master_rlast_int;      // last transfer in burst
   logic [SH_NB_BANKS-1:0][ AXI_USER-1:0]              axi_master_ruser_int;      //
   logic [SH_NB_BANKS-1:0]                             axi_master_rvalid_int;     // slave data valid
   logic [SH_NB_BANKS-1:0]                             axi_master_rready_int;     // master ready to accept

   logic [NB_CORES - 1 :0][31:0]                         congestion_counter;


   genvar i;
   generate

`ifdef FEATURE_ICACHE_STAT

      case (SH_NB_BANKS)
         1: begin
                        for(i=0;i<NB_CORES;i++)
                        begin : STAT_CONGESTION_COUNT_SINGLE_BANK
                            always_ff @(posedge clk, negedge rst_n)
                            begin
                                if(~rst_n)
                                begin
                                        congestion_counter[i] <= '0;
                                end
                                else
                                begin
                                    if( IC_ctrl_unit_bus_pri[i].ctrl_clear_regs )
                                    begin
                                        congestion_counter[i] <= '0;
                                    end
                                    else
                                    begin
                                        if( IC_ctrl_unit_bus_pri[i].ctrl_enable_regs )
                                        begin
                                             if( refill_req_int[i] & ~refill_gnt_int[i] & fetch_gnt_from_main_cache[0] )
                                                congestion_counter[i] <= congestion_counter[i] + 1'b1;

                                        end
                                    end

                                end
                            end
                        end
         end

         default : begin
                        for(i=0;i<NB_CORES;i++)
                        begin : STAT_CONGESTION_COUNT_MULTI_BANK
                            always_ff @(posedge clk, negedge rst_n)
                            begin
                                if(~rst_n)
                                begin
                                        congestion_counter[i] <= '0;
                                end
                                else
                                begin
                                    if( IC_ctrl_unit_bus_pri[i].ctrl_clear_regs )
                                    begin
                                        congestion_counter[i] <= '0;
                                    end
                                    else
                                    begin
                                        if( IC_ctrl_unit_bus_pri[i].ctrl_enable_regs )
                                        begin
                                             if( refill_req_int[i] & ~refill_gnt_int[i] & fetch_gnt_from_main_cache[ refill_addr_int[i][ADDR_OFFSET+$clog2(SH_NB_BANKS)-1:ADDR_OFFSET] ]   )
                                                congestion_counter[i] <= congestion_counter[i] + 1'b1;
                                        end
                                    end

                                end
                            end
                        end
         end

      endcase
`endif

      ////////////////////////////////////////////////////////////////////////////////////
      // ██████╗ ██████╗ ██╗        ██╗ ██████╗ █████╗  ██████╗██╗  ██╗███████╗███████╗ //
      // ██╔══██╗██╔══██╗██║        ██║██╔════╝██╔══██╗██╔════╝██║  ██║██╔════╝██╔════╝ //
      // ██████╔╝██████╔╝██║        ██║██║     ███████║██║     ███████║█████╗  ███████╗ //
      // ██╔═══╝ ██╔══██╗██║        ██║██║     ██╔══██║██║     ██╔══██║██╔══╝  ╚════██║ //
      // ██║     ██║  ██║██║███████╗██║╚██████╗██║  ██║╚██████╗██║  ██║███████╗███████║ //
      // ╚═╝     ╚═╝  ╚═╝╚═╝╚══════╝╚═╝ ╚═════╝╚═╝  ╚═╝ ╚═════╝╚═╝  ╚═╝╚══════╝╚══════╝ //
      ////////////////////////////////////////////////////////////////////////////////////
      for(i=0;i<NB_CORES;i++)
      begin : PRI_ICACHE

         assign IC_ctrl_unit_bus_pri[i].ctrl_cong_count = congestion_counter[i];

         pri_icache
         #(
            .FETCH_ADDR_WIDTH     ( FETCH_ADDR_WIDTH ), //= 32,       // Size of the fetch address
            .FETCH_DATA_WIDTH     ( FETCH_DATA_WIDTH ), //= 128,      // Size of the fetch data

            .NB_WAYS              ( PRI_NB_WAYS      ), //= 4,        // Cache associativity
            .CACHE_SIZE           ( PRI_CACHE_SIZE   ), //= 512      // Ccache capacity in Byte
            .CACHE_LINE           ( PRI_CACHE_LINE   ), //= 1,        // in word of [FETCH_DATA_WIDTH]

            .USE_REDUCED_TAG      ( USE_REDUCED_TAG  ), //= "TRUE",   // TRUE | FALSE
            .L2_SIZE              ( L2_SIZE          ) //= 512*1024  // Size of max(L2 ,ROM) program memory in Byte
         )
         i_pri_icache
         (
            .clk                  ( clk                                          ),
            .rst_n                ( rst_n                                        ),
            .test_en_i            ( test_en_i                                    ),

            .fetch_req_i          ( fetch_req_i[i]                               ),
            .fetch_addr_i         ( fetch_addr_i[i]                              ),
            .fetch_gnt_o          ( fetch_gnt_o[i]                               ),
            .fetch_rvalid_o       ( fetch_rvalid_o[i]                            ),
            .fetch_rdata_o        ( fetch_rdata_o[i]                             ),

            .refill_req_o         ( refill_req_int[i]                            ),
            .refill_gnt_i         ( refill_gnt_int[i]                            ),
            .refill_addr_o        ( refill_addr_int[i]                           ),
            .refill_r_valid_i     ( refill_r_valid_int[i]                        ),
            .refill_r_data_i      ( refill_r_data_int[i]                         ),

            .pre_refill_req_o     ( refill_req_int[NB_CORES+i]                   ),
            .pre_refill_gnt_i     ( refill_gnt_int[NB_CORES+i]                   ),
            .pre_refill_addr_o    ( refill_addr_int[NB_CORES+i]                  ),
            .pre_refill_r_valid_i ( refill_r_valid_int[NB_CORES+i]               ),
            .pre_refill_r_data_i  ( refill_r_data_int[NB_CORES+i]                ),

            .enable_l1_l15_prefetch_i ( enable_l1_l15_prefetch_i[i]              ),

            .bypass_icache_i      ( IC_ctrl_unit_bus_pri[i].bypass_req           ),
            .cache_is_bypassed_o  ( IC_ctrl_unit_bus_pri[i].bypass_ack           ),
            .flush_icache_i       ( IC_ctrl_unit_bus_pri[i].flush_req            ),
            .cache_is_flushed_o   ( IC_ctrl_unit_bus_pri[i].flush_ack            ),
            .flush_set_ID_req_i   ( IC_ctrl_unit_bus_pri[i].sel_flush_req        ),
            .flush_set_ID_addr_i  ( IC_ctrl_unit_bus_pri[i].sel_flush_addr       ),
            .flush_set_ID_ack_o   ( IC_ctrl_unit_bus_pri[i].sel_flush_ack        )

        `ifdef FEATURE_ICACHE_STAT
             ,
             .bank_hit_count_o    ( IC_ctrl_unit_bus_pri[i].ctrl_hit_count       ),
             .bank_trans_count_o  ( IC_ctrl_unit_bus_pri[i].ctrl_trans_count     ),
             .bank_miss_count_o   ( IC_ctrl_unit_bus_pri[i].ctrl_miss_count      ),

             .ctrl_clear_regs_i   ( IC_ctrl_unit_bus_pri[i].ctrl_clear_regs      ),
             .ctrl_enable_regs_i  ( IC_ctrl_unit_bus_pri[i].ctrl_enable_regs     )
        `endif
         );
      end
   endgenerate

   ////////////////////////////////////////////////////////////////////////////////////
   // ██╗ ██████╗ █████╗  ██████╗██╗  ██╗███████╗    ██╗███╗   ██╗████████╗ ██████╗  //
   // ██║██╔════╝██╔══██╗██╔════╝██║  ██║██╔════╝    ██║████╗  ██║╚══██╔══╝██╔════╝  //
   // ██║██║     ███████║██║     ███████║█████╗      ██║██╔██╗ ██║   ██║   ██║       //
   // ██║██║     ██╔══██║██║     ██╔══██║██╔══╝      ██║██║╚██╗██║   ██║   ██║       //
   // ██║╚██████╗██║  ██║╚██████╗██║  ██║███████╗    ██║██║ ╚████║   ██║   ╚██████╗  //
   // ╚═╝ ╚═════╝╚═╝  ╚═╝ ╚═════╝╚═╝  ╚═╝╚══════╝    ╚═╝╚═╝  ╚═══╝   ╚═╝    ╚═════╝  //
   ////////////////////////////////////////////////////////////////////////////////////
   // -----------------------------------------------------------------------------------------
   // Read Only INTERCONNECT   MULTIPLEX different request from cores (not the HW PF)  --------
   // SHARED_ICACHE_INTERCONNECT                                                       --------
   // -----------------------------------------------------------------------------------------

   // Eg 9 COres: --> NCH_0 = 8, NCH_1= 1;
   localparam N_CH0 = (2**$clog2( 2*NB_CORES ) == 2*NB_CORES) ? 2*NB_CORES : 2**$clog2( 2*NB_CORES-1);
   localparam N_CH1 = (2**$clog2( 2*NB_CORES ) == 2*NB_CORES) ? 0       : 2*NB_CORES - 2**$clog2( 2*NB_CORES-1);

   icache_intc
   #(
      .ADDRESS_WIDTH  ( FETCH_ADDR_WIDTH                 ),
      .N_CORES        ( N_CH0                            ),
      .N_AUX_CHANNEL  ( N_CH1                            ),
      .UID_WIDTH      ( 2*NB_CORES                       ),
      .DATA_WIDTH     ( FETCH_DATA_WIDTH                 ),
      .N_CACHE_BANKS  ( SH_NB_BANKS                      ) // Single L1.5 cache
   )
   ICACHE_INTERCONNECT
   (
      .clk_i          ( clk                              ),
      .rst_ni         ( rst_n                            ),

      .request_i      ( refill_req_int                   ), // Data request
      .address_i      ( refill_addr_int                  ), // Data request Address
      .grant_o        ( refill_gnt_int                   ), //
      .response_o     ( refill_r_valid_int               ), // Data Response Valid (For LOAD/STORE commands)
      .read_data_o    ( refill_r_data_int                ), // Data Response DATA (For LOAD commands)

      .request_o      ( fetch_req_to_main_cache          ), // Data request
      .address_o      ( fetch_addr_to_main_cache         ), // Data request Address
      .UID_o          ( fetch_ID_to_main_cache           ), // Data request Address
      .grant_i        ( fetch_gnt_from_main_cache        ), // Data Grant
      .read_data_i    ( fetch_rdata_from_main_cache      ), // valid REspone (must be accepted always)
      .response_i     ( fetch_rvalid_from_to_main_cache  ), // Data Response ID (For LOAD commands)
      .response_UID_i ( fetch_rID_from_main_cache        )  // Data Response DATA (For LOAD and STORE)
   );




   generate

   /////////////////////////////////////////////////////////////////////////////////////////
   // ███╗   ███╗ █████╗ ██╗███╗   ██╗        ██╗ ██████╗ █████╗  ██████╗██╗  ██╗███████╗ //
   // ████╗ ████║██╔══██╗██║████╗  ██║        ██║██╔════╝██╔══██╗██╔════╝██║  ██║██╔════╝ //
   // ██╔████╔██║███████║██║██╔██╗ ██║        ██║██║     ███████║██║     ███████║█████╗   //
   // ██║╚██╔╝██║██╔══██║██║██║╚██╗██║        ██║██║     ██╔══██║██║     ██╔══██║██╔══╝   //
   // ██║ ╚═╝ ██║██║  ██║██║██║ ╚████║███████╗██║╚██████╗██║  ██║╚██████╗██║  ██║███████╗ //
   // ╚═╝     ╚═╝╚═╝  ╚═╝╚═╝╚═╝  ╚═══╝╚══════╝╚═╝ ╚═════╝╚═╝  ╚═╝ ╚═════╝╚═╝  ╚═╝╚══════╝ //
   /////////////////////////////////////////////////////////////////////////////////////////
   for (i=0; i<  SH_NB_BANKS; i++)
   begin : Main_Icache
   share_icache
   #(
      .N_BANKS                ( SH_NB_BANKS                    ),
      .SET_ASSOCIATIVE        ( SH_NB_WAYS                     ),
      .CACHE_LINE             ( SH_CACHE_LINE                  ),
      .CACHE_SIZE             ( SH_CACHE_SIZE/SH_NB_BANKS      ),  //In Byte
      .CACHE_ID               ( i                              ),
      .FIFO_DEPTH             ( 4                              ),

      .ICACHE_DATA_WIDTH      ( FETCH_DATA_WIDTH               ),
      .ICACHE_ID_WIDTH        ( 2*NB_CORES                     ),
      .ICACHE_ADDR_WIDTH      ( FETCH_ADDR_WIDTH               ),

      .DIRECT_MAPPED_FEATURE  ( "DISABLED"                     ),

      .AXI_ID                 ( AXI_ID_INT                     ),
      .AXI_ADDR               ( AXI_ADDR                       ),
      .AXI_DATA               ( AXI_DATA                       ),
      .AXI_USER               ( AXI_USER                       ),

      .USE_REDUCED_TAG        ( USE_REDUCED_TAG                ),
      .L2_SIZE                ( L2_SIZE                        )
   )
   i_main_shared_icache
   (
      // ---------------------------------------------------------------
      // I/O Port Declarations -----------------------------------------
      // ---------------------------------------------------------------
      .clk                           ( clk                        ),
      .rst_n                         ( rst_n                      ),
      .test_en_i                     ( test_en_i                  ),

      // DFT ports
      .mem_ctrl,
      .dft_ram_gt_se,
      .dft_ram_bypass,
      .dft_ram_bp_clk_en,

      // ---------------------------------------------------------------
      // SHARED_ICACHE_INTERCONNECT Port Declarations -----------------------------------------
      // -----------------           ----------------------------------------------
      .fetch_req_i                   (  fetch_req_to_main_cache[i]         ),
      .fetch_grant_o                 (  fetch_gnt_from_main_cache[i]       ),
      .fetch_addr_i                  (  fetch_addr_to_main_cache[i]        ),
      .fetch_ID_i                    (  fetch_ID_to_main_cache[i]          ),
      .fetch_r_rdata_o               (  fetch_rdata_from_main_cache[i]     ),
      .fetch_r_valid_o               (  fetch_rvalid_from_to_main_cache[i] ),
      .fetch_r_ID_o                  (  fetch_rID_from_main_cache[i]       ),

      // §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ //
      // §§§§§§§§§§§§§§§§§§§    REFILL Request side  §§§§§§§§§§§§§§§§§§§§§§§ //
      // §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ //
      .init_awid_o                   ( axi_master_awid_int[i]     ),
      .init_awaddr_o                 ( axi_master_awaddr_int[i]   ),
      .init_awlen_o                  ( axi_master_awlen_int[i]    ),
      .init_awsize_o                 ( axi_master_awsize_int[i]   ),
      .init_awburst_o                ( axi_master_awburst_int[i]  ),
      .init_awlock_o                 ( axi_master_awlock_int[i]   ),
      .init_awcache_o                ( axi_master_awcache_int[i]  ),
      .init_awprot_o                 ( axi_master_awprot_int[i]   ),
      .init_awregion_o               ( axi_master_awregion_int[i] ),
      .init_awuser_o                 ( axi_master_awuser_int[i]   ),
      .init_awqos_o                  ( axi_master_awqos_int[i]    ),
      .init_awvalid_o                ( axi_master_awvalid_int[i]  ),
      .init_awready_i                ( axi_master_awready_int[i]  ),

      .init_wdata_o                  ( axi_master_wdata_int[i]    ),
      .init_wstrb_o                  ( axi_master_wstrb_int[i]    ),
      .init_wlast_o                  ( axi_master_wlast_int[i]    ),
      .init_wuser_o                  ( axi_master_wuser_int[i]    ),
      .init_wvalid_o                 ( axi_master_wvalid_int[i]   ),
      .init_wready_i                 ( axi_master_wready_int[i]   ),

      .init_bid_i                    ( axi_master_bid_int[i]      ),
      .init_bresp_i                  ( axi_master_bresp_int[i]    ),
      .init_buser_i                  ( axi_master_buser_int[i]    ),
      .init_bvalid_i                 ( axi_master_bvalid_int[i]   ),
      .init_bready_o                 ( axi_master_bready_int[i]   ),

      .init_arid_o                   ( axi_master_arid_int[i]     ),
      .init_araddr_o                 ( axi_master_araddr_int[i]   ),
      .init_arlen_o                  ( axi_master_arlen_int[i]    ),
      .init_arsize_o                 ( axi_master_arsize_int[i]   ),
      .init_arburst_o                ( axi_master_arburst_int[i]  ),
      .init_arlock_o                 ( axi_master_arlock_int[i]   ),
      .init_arcache_o                ( axi_master_arcache_int[i]  ),
      .init_arprot_o                 ( axi_master_arprot_int[i]   ),
      .init_arregion_o               ( axi_master_arregion_int[i] ),
      .init_aruser_o                 ( axi_master_aruser_int[i]   ),
      .init_arqos_o                  ( axi_master_arqos_int[i]    ),
      .init_arvalid_o                ( axi_master_arvalid_int[i]  ),
      .init_arready_i                ( axi_master_arready_int[i]  ),

      .init_rid_i                    ( axi_master_rid_int[i]       ),
      .init_rdata_i                  ( axi_master_rdata_int[i]     ),
      .init_rresp_i                  ( axi_master_rresp_int[i]     ),
      .init_rlast_i                  ( axi_master_rlast_int[i]     ),
      .init_ruser_i                  ( axi_master_ruser_int[i]     ),
      .init_rvalid_i                 ( axi_master_rvalid_int[i]    ),
      .init_rready_o                 ( axi_master_rready_int[i]    ),

      // Control ports
      .ctrl_req_enable_icache_i      ( IC_ctrl_unit_bus_main[i].ctrl_req_enable      ),
      .ctrl_ack_enable_icache_o      ( IC_ctrl_unit_bus_main[i].ctrl_ack_enable      ),
      .ctrl_req_disable_icache_i     ( IC_ctrl_unit_bus_main[i].ctrl_req_disable     ),
      .ctrl_ack_disable_icache_o     ( IC_ctrl_unit_bus_main[i].ctrl_ack_disable     ),
      .ctrl_req_flush_icache_i       ( IC_ctrl_unit_bus_main[i].ctrl_flush_req       ),
      .ctrl_ack_flush_icache_o       ( IC_ctrl_unit_bus_main[i].ctrl_flush_ack       ),
      .ctrl_pending_trans_icache_o   ( IC_ctrl_unit_bus_main[i].ctrl_pending_trans   ),
      .ctrl_sel_flush_req_i          ( IC_ctrl_unit_bus_main[i].sel_flush_req        ),
      .ctrl_sel_flush_addr_i         ( IC_ctrl_unit_bus_main[i].sel_flush_addr       ),
      .ctrl_sel_flush_ack_o          ( IC_ctrl_unit_bus_main[i].sel_flush_ack        )
   `ifdef FEATURE_ICACHE_STAT
      ,
      .ctrl_hit_count_icache_o       ( IC_ctrl_unit_bus_main[i].ctrl_hit_count    ),
      .ctrl_trans_count_icache_o     ( IC_ctrl_unit_bus_main[i].ctrl_trans_count  ),
      .ctrl_miss_count_icache_o      ( IC_ctrl_unit_bus_main[i].ctrl_miss_count   ),
      .ctrl_clear_regs_icache_i      ( IC_ctrl_unit_bus_main[i].ctrl_clear_regs   ),
      .ctrl_enable_regs_icache_i     ( IC_ctrl_unit_bus_main[i].ctrl_enable_regs   )
   `endif
   );
   end
endgenerate




generate

   case(SH_NB_BANKS)

   1: begin : SINGLE_L1p5_BANK
      assign axi_master_awid_o      = { {(AXI_ID - AXI_ID_INT){1'b0}}, axi_master_awid_int};
      assign axi_master_awaddr_o    = axi_master_awaddr_int;
      assign axi_master_awlen_o     = axi_master_awlen_int;
      assign axi_master_awsize_o    = axi_master_awsize_int;
      assign axi_master_awburst_o   = axi_master_awburst_int;
      assign axi_master_awlock_o    = axi_master_awlock_int;
      assign axi_master_awcache_o   = axi_master_awcache_int | 4'b0010; // make modifiable
      assign axi_master_awprot_o    = axi_master_awprot_int;
      assign axi_master_awregion_o  = axi_master_awregion_int;
      assign axi_master_awuser_o    = axi_master_awuser_int;
      assign axi_master_awqos_o     = axi_master_awqos_int;
      assign axi_master_awvalid_o   = axi_master_awvalid_int;
      assign axi_master_awready_int = axi_master_awready_i;

      assign axi_master_wdata_o    = axi_master_wdata_int;
      assign axi_master_wstrb_o    = axi_master_wstrb_int;
      assign axi_master_wlast_o    = axi_master_wlast_int;
      assign axi_master_wuser_o    = axi_master_wuser_int;
      assign axi_master_wvalid_o   = axi_master_wvalid_int;
      assign axi_master_wready_int = axi_master_wready_i;

      assign axi_master_bid_int    = axi_master_bid_i[AXI_ID_INT-1:0];
      assign axi_master_bresp_int  = axi_master_bresp_i;
      assign axi_master_buser_int  = axi_master_buser_i;
      assign axi_master_bvalid_int = axi_master_bvalid_i;
      assign axi_master_bready_o   = axi_master_bready_int;

      assign axi_master_arid_o      = { {(AXI_ID - AXI_ID_INT){1'b0}}, axi_master_arid_int};
      assign axi_master_araddr_o    = axi_master_araddr_int;
      assign axi_master_arlen_o     = axi_master_arlen_int;
      assign axi_master_arsize_o    = axi_master_arsize_int;
      assign axi_master_arburst_o   = axi_master_arburst_int;
      assign axi_master_arlock_o    = axi_master_arlock_int;
      assign axi_master_arcache_o   = axi_master_arcache_int | 4'b0010; // make modifiable
      assign axi_master_arprot_o    = axi_master_arprot_int;
      assign axi_master_arregion_o  = axi_master_arregion_int;
      assign axi_master_aruser_o    = axi_master_aruser_int;
      assign axi_master_arqos_o     = axi_master_arqos_int;
      assign axi_master_arvalid_o   = axi_master_arvalid_int;
      assign axi_master_arready_int = axi_master_arready_i;

      assign axi_master_rid_int     = axi_master_rid_i[AXI_ID_INT-1:0];
      assign axi_master_rdata_int   = axi_master_rdata_i;
      assign axi_master_rresp_int   = axi_master_rresp_i;
      assign axi_master_rlast_int   = axi_master_rlast_i;
      assign axi_master_ruser_int   = axi_master_ruser_i;
      assign axi_master_rvalid_int  = axi_master_rvalid_i;
      assign axi_master_rready_o    = axi_master_rready_int;
   end

   default:
   begin : MULTI_L1p5_BANK

      localparam N_MASTER_PORT = 1;
      localparam N_REGION      = 1;

      logic [N_REGION-1:0][N_MASTER_PORT-1:0][31:0]                      cfg_START_ADDR_int;
      logic [N_REGION-1:0][N_MASTER_PORT-1:0][31:0]                      cfg_END_ADDR_int;
      logic [N_REGION-1:0][N_MASTER_PORT-1:0]                            cfg_valid_rule_int;
      logic [SH_NB_BANKS-1:0][N_MASTER_PORT-1:0]                       cfg_connectivity_map_int;

      assign cfg_START_ADDR_int[0][0]       = 32'h0000_0000;
      assign cfg_END_ADDR_int[0][0]         = 32'hFFFF_FFFF;
      assign cfg_valid_rule_int[0][0]       = 1'b1;



      for(i=0; i<SH_NB_BANKS; i++)
         assign cfg_connectivity_map_int[i][0]       = 1'b1;

      /////////////////////////////////////////////////////////////////
      //  █████╗ ██╗  ██╗██╗    ███╗   ██╗ ██████╗ ██████╗ ███████╗  //
      // ██╔══██╗╚██╗██╔╝██║    ████╗  ██║██╔═══██╗██╔══██╗██╔════╝  //
      // ███████║ ╚███╔╝ ██║    ██╔██╗ ██║██║   ██║██║  ██║█████╗    //
      // ██╔══██║ ██╔██╗ ██║    ██║╚██╗██║██║   ██║██║  ██║██╔══╝    //
      // ██║  ██║██╔╝ ██╗██║    ██║ ╚████║╚██████╔╝██████╔╝███████╗  //
      // ╚═╝  ╚═╝╚═╝  ╚═╝╚═╝    ╚═╝  ╚═══╝ ╚═════╝ ╚═════╝ ╚══════╝  //
      /////////////////////////////////////////////////////////////////
      logic [3:0] axi_master_awcache, axi_master_arcache;
      axi_node
      #(

          .AXI_ADDRESS_W      ( AXI_ADDR                 ),
          .AXI_DATA_W         ( AXI_DATA                 ),
          .AXI_NUMBYTES       ( AXI_DATA/8               ),

          .AXI_USER_W         ( AXI_USER                 ),
          .AXI_ID_IN          ( AXI_ID_INT               ),
          .AXI_ID_OUT         ( AXI_ID_OUT               ),

          .N_MASTER_PORT      ( 1                        ),
          .N_SLAVE_PORT       ( SH_NB_BANKS              ),


          .FIFO_DEPTH_DW      ( 2                        ),
          .N_REGION           ( 1                        )
      )
      AXI_INTRUCTION_BUS
      (
        .clk                  (  clk                    ),
        .rst_n                (  rst_n                  ),
        .test_en_i            (  test_en_i              ),

        // ---------------------------------------------------------------
        // AXI TARG Port Declarations -----------------------------------------
        // ---------------------------------------------------------------
        .slave_awid_i          ( axi_master_awid_int      ),
        .slave_awaddr_i        ( axi_master_awaddr_int    ),
        .slave_awlen_i         ( axi_master_awlen_int     ),
        .slave_awsize_i        ( axi_master_awsize_int    ),
        .slave_awburst_i       ( axi_master_awburst_int   ),
        .slave_awlock_i        ( axi_master_awlock_int    ),
        .slave_awcache_i       ( axi_master_awcache_int   ),
        .slave_awprot_i        ( axi_master_awprot_int    ),
        .slave_awregion_i      ( axi_master_awregion_int  ),
        .slave_awatop_i        ( '0 /* unused */          ),
        .slave_awuser_i        ( axi_master_awuser_int    ),
        .slave_awqos_i         ( axi_master_awqos_int     ),
        .slave_awvalid_i       ( axi_master_awvalid_int   ),
        .slave_awready_o       ( axi_master_awready_int   ),

        .slave_wdata_i         ( axi_master_wdata_int     ),
        .slave_wstrb_i         ( axi_master_wstrb_int     ),
        .slave_wlast_i         ( axi_master_wlast_int     ),
        .slave_wuser_i         ( axi_master_wuser_int     ),
        .slave_wvalid_i        ( axi_master_wvalid_int    ),
        .slave_wready_o        ( axi_master_wready_int    ),


        .slave_bid_o           ( axi_master_bid_int       ),
        .slave_bresp_o         ( axi_master_bresp_int     ),
        .slave_bvalid_o        ( axi_master_bvalid_int    ),
        .slave_buser_o         ( axi_master_buser_int     ),
        .slave_bready_i        ( axi_master_bready_int    ),


        .slave_arid_i          ( axi_master_arid_int      ),
        .slave_araddr_i        ( axi_master_araddr_int    ),
        .slave_arlen_i         ( axi_master_arlen_int     ),
        .slave_arsize_i        ( axi_master_arsize_int    ),
        .slave_arburst_i       ( axi_master_arburst_int   ),
        .slave_arlock_i        ( axi_master_arlock_int    ),
        .slave_arcache_i       ( axi_master_arcache_int   ),
        .slave_arprot_i        ( axi_master_arprot_int    ),
        .slave_arregion_i      ( axi_master_arregion_int  ),
        .slave_aruser_i        ( axi_master_aruser_int    ),
        .slave_arqos_i         ( axi_master_arqos_int     ),
        .slave_arvalid_i       ( axi_master_arvalid_int   ),
        .slave_arready_o       ( axi_master_arready_int   ),
        // -----------------------------------------------

        .slave_rid_o           ( axi_master_rid_int       ),
        .slave_rdata_o         ( axi_master_rdata_int     ),
        .slave_rresp_o         ( axi_master_rresp_int     ),
        .slave_rlast_o         ( axi_master_rlast_int     ),
        .slave_ruser_o         ( axi_master_ruser_int     ),
        .slave_rvalid_o        ( axi_master_rvalid_int    ),
        .slave_rready_i        ( axi_master_rready_int    ),
        // -----------------------------------------------

        // -----------------------------------------------
        // AXI INIT Port Declarations --------------------
        // -----------------------------------------------
        .master_awid_o          ( axi_master_awid_o[AXI_ID_OUT-1:0] ),
        .master_awaddr_o        ( axi_master_awaddr_o               ),
        .master_awlen_o         ( axi_master_awlen_o                ),
        .master_awsize_o        ( axi_master_awsize_o               ),
        .master_awburst_o       ( axi_master_awburst_o              ),
        .master_awlock_o        ( axi_master_awlock_o               ),
        .master_awcache_o       ( axi_master_awcache                ),
        .master_awprot_o        ( axi_master_awprot_o               ),
        .master_awregion_o      ( axi_master_awregion_o             ),
        .master_awatop_o        ( /* unused */                      ),
        .master_awuser_o        ( axi_master_awuser_o               ),
        .master_awqos_o         ( axi_master_awqos_o                ),
        .master_awvalid_o       ( axi_master_awvalid_o              ),
        .master_awready_i       ( axi_master_awready_i              ),

        .master_wdata_o         ( axi_master_wdata_o                ),
        .master_wstrb_o         ( axi_master_wstrb_o                ),
        .master_wlast_o         ( axi_master_wlast_o                ),
        .master_wuser_o         ( axi_master_wuser_o                ),
        .master_wvalid_o        ( axi_master_wvalid_o               ),
        .master_wready_i        ( axi_master_wready_i               ),

        .master_bid_i           ( axi_master_bid_i[AXI_ID_OUT-1:0]  ),
        .master_bresp_i         ( axi_master_bresp_i                ),
        .master_buser_i         ( axi_master_buser_i                ),
        .master_bvalid_i        ( axi_master_bvalid_i               ),
        .master_bready_o        ( axi_master_bready_o               ),

        .master_arid_o          ( axi_master_arid_o[AXI_ID_OUT-1:0] ),
        .master_araddr_o        ( axi_master_araddr_o               ),
        .master_arlen_o         ( axi_master_arlen_o                ),
        .master_arsize_o        ( axi_master_arsize_o               ),
        .master_arburst_o       ( axi_master_arburst_o              ),
        .master_arlock_o        ( axi_master_arlock_o               ),
        .master_arcache_o       ( axi_master_arcache                ),
        .master_arprot_o        ( axi_master_arprot_o               ),
        .master_arregion_o      ( axi_master_arregion_o             ),
        .master_aruser_o        ( axi_master_aruser_o               ),
        .master_arqos_o         ( axi_master_arqos_o                ),
        .master_arvalid_o       ( axi_master_arvalid_o              ),
        .master_arready_i       ( axi_master_arready_i              ),

        .master_rid_i           ( axi_master_rid_i[AXI_ID_OUT-1:0]  ),
        .master_rdata_i         ( axi_master_rdata_i                ),
        .master_rresp_i         ( axi_master_rresp_i                ),
        .master_rlast_i         ( axi_master_rlast_i                ),
        .master_ruser_i         ( axi_master_ruser_i                ),
        .master_rvalid_i        ( axi_master_rvalid_i               ),
        .master_rready_o        ( axi_master_rready_o               ),

        .cfg_START_ADDR_i       ( cfg_START_ADDR_int                ),
        .cfg_END_ADDR_i         ( cfg_END_ADDR_int                  ),
        .cfg_valid_rule_i       ( cfg_valid_rule_int                ),
        .cfg_connectivity_map_i ( cfg_connectivity_map_int          )

      );
      assign axi_master_awcache_o = axi_master_awcache | 4'b0010; // make modifiable
      assign axi_master_arcache_o = axi_master_arcache | 4'b0010; // make modifiable

      assign     axi_master_awid_o[AXI_ID-1:AXI_ID_OUT] = {(AXI_ID-AXI_ID_OUT){1'b0}};
      assign     axi_master_arid_o[AXI_ID-1:AXI_ID_OUT] = {(AXI_ID-AXI_ID_OUT){1'b0}};
   end

   endcase
endgenerate

endmodule // icache_hier_top
