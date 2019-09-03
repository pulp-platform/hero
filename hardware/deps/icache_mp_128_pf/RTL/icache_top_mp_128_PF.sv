////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Copyright 2018 ETH Zurich and University of Bologna.                       //
// Copyright and related rights are licensed under the Solderpad Hardware     //
// License, Version 0.51 (the "License"); you may not use this file except in //
// compliance with the License.  You may obtain a copy of the License at      //
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law  //
// or agreed to in writing, software, hardware and materials distributed under//
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR     //
// CONDITIONS OF ANY KIND, either express or implied. See the License for the //
// specific language governing permissions and limitations under the License. //
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
// Create Date:    22/01/2018                                                 //
// Design Name:    ICACHE_MP_128_PF                                           //
// Module Name:    icache_top_mp_128_PF                                       //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    This block represents the top module for the shared cache  //
//                 It instanciates the master cache controller, the TAG/DATA  //
//                 array and the HW prefetcher.                               //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 22/01/2018 : File Created                                  //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`define  USE_AXI_SLICES

module icache_top_mp_128_PF
#(
   parameter int    FETCH_ADDR_WIDTH  = 32,
   parameter int    FETCH_DATA_WIDTH  = 128,

   parameter int    NB_CORES          = 8,
   parameter int    NB_BANKS          = 8,
   parameter int    NB_WAYS           = 4,
   parameter int    CACHE_SIZE        = 4096, // in Byte
   parameter int    CACHE_LINE        = 1,    // in word of [FETCH_DATA_WIDTH]

   parameter bit    FEATURE_STAT      = 1'b0,

   parameter int    AXI_ID            = 6,
   parameter int    AXI_ADDR          = 32,
   parameter int    AXI_USER          = 6,
   parameter int    AXI_DATA          = 64,

   parameter bit    USE_REDUCED_TAG   = 1'b1,
   parameter int    L2_SIZE           = 512*1024    // Size of max(L2 ,ROM) program memory in Byte
)
(
   input logic                                           clk,
   input logic                                           rst_n,
   input logic                                           test_en_i,

   // interface with processors
   input  logic [NB_CORES-1:0]                           fetch_req_i,
   input  logic [NB_CORES-1:0][FETCH_ADDR_WIDTH-1:0]     fetch_addr_i,
   output logic [NB_CORES-1:0]                           fetch_gnt_o,

   output logic [NB_CORES-1:0]                           fetch_rvalid_o,
   output logic [NB_CORES-1:0][FETCH_DATA_WIDTH-1:0]     fetch_rdata_o,



   //AXI read address bus -------------------------------------------
   output  logic [AXI_ID-1:0]                            axi_master_arid_o,
   output  logic [AXI_ADDR-1:0]                          axi_master_araddr_o,
   output  logic [ 7:0]                                  axi_master_arlen_o,    //burst length - 1 to 16
   output  logic [ 2:0]                                  axi_master_arsize_o,   //size of each transfer in burst
   output  logic [ 1:0]                                  axi_master_arburst_o,  //for bursts>1, accept only incr burst=01
   output  logic                                         axi_master_arlock_o,   //only normal access supported axs_awlock=00
   output  logic [ 3:0]                                  axi_master_arcache_o, 
   output  logic [ 2:0]                                  axi_master_arprot_o,
   output  logic [ 3:0]                                  axi_master_arregion_o, //
   output  logic [ AXI_USER-1:0]                         axi_master_aruser_o,   //
   output  logic [ 3:0]                                  axi_master_arqos_o,    //  
   output  logic                                         axi_master_arvalid_o,  //master addr valid
   input logic                                           axi_master_arready_i,  //slave ready to accept
   // ---------------------------------------------------------------


   //AXI BACKWARD read data bus ----------------------------------------------
   input   logic [AXI_ID-1:0]                            axi_master_rid_i,
   input   logic [AXI_DATA-1:0]                          axi_master_rdata_i,
   input   logic [1:0]                                   axi_master_rresp_i,
   input   logic                                         axi_master_rlast_i,    //last transfer in burst
   input   logic [AXI_USER-1:0]                          axi_master_ruser_i,
   input   logic                                         axi_master_rvalid_i,   //slave data valid
   output  logic                                         axi_master_rready_o,    //master ready to accept

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

   MP_PF_ICACHE_CTRL_UNIT_BUS.Slave                      IC_ctrl_unit_slave_if
);

   // Parameter to reduce the TAG bits (cachin only L2 and not on 4GB memory space)
   // The assumption is that During ROM reading cache is Disabled.
   localparam REDUCE_TAG_WIDTH   = $clog2(L2_SIZE/CACHE_SIZE)+$clog2(NB_WAYS);

   localparam OFFSET             = $clog2(FETCH_DATA_WIDTH)-3; // log2(128)-3 = 4;
   localparam BANK_SIZE          = CACHE_SIZE/NB_BANKS;
   localparam WAY_SIZE           = BANK_SIZE/NB_WAYS;
   localparam SCM_NUM_ROWS       = WAY_SIZE/(CACHE_LINE*FETCH_DATA_WIDTH/8); // TAG
   localparam SCM_TAG_ADDR_WIDTH = $clog2(SCM_NUM_ROWS);

   localparam TAG_WIDTH          = USE_REDUCED_TAG ? REDUCE_TAG_WIDTH : (FETCH_ADDR_WIDTH - SCM_TAG_ADDR_WIDTH - $clog2(NB_BANKS) - $clog2(CACHE_LINE) - OFFSET + 1);
 
   localparam DATA_WIDTH          = FETCH_DATA_WIDTH;
   localparam SCM_DATA_ADDR_WIDTH = SCM_TAG_ADDR_WIDTH; 

   localparam AXI_ID_INT          = $clog2(NB_CORES+1);

   localparam SET_ID_LSB          = $clog2(NB_BANKS)+$clog2(FETCH_DATA_WIDTH*CACHE_LINE)-3;
   localparam SET_ID_MSB          = SET_ID_LSB + SCM_TAG_ADDR_WIDTH - 1;
   localparam TAG_LSB             = SET_ID_MSB + 1;
   localparam TAG_MSB             = TAG_LSB + TAG_WIDTH - 2 ; //1 bit is count for valid


   // interface with READ PORT --> SCM DATA
   logic [NB_CORES-1:0][NB_BANKS-1:0]                                      DATA_read_req_int;   
   logic [NB_CORES-1:0][SCM_DATA_ADDR_WIDTH-1:0]                           DATA_read_addr_int;
   logic [NB_BANKS-1:0][NB_WAYS-1:0][NB_CORES-1:0][FETCH_DATA_WIDTH-1:0]   DATA_read_rdata_int;

   // interface with READ PORT --> SCM TAG
   logic [NB_CORES:0][NB_BANKS-1:0]                                        TAG_read_req_int;   
   logic [NB_CORES:0][SCM_TAG_ADDR_WIDTH-1:0]                              TAG_read_addr_int;
   logic [NB_BANKS-1:0][NB_WAYS-1:0][NB_CORES:0][TAG_WIDTH-1:0]            TAG_read_rdata_int;


   // interface with WRITE PORT --> TAG SCM UNIFIED
   logic                                                                   SCM_TAG_write_req_int;
   logic [SCM_TAG_ADDR_WIDTH-1:0]                                          SCM_TAG_write_addr_int;
   logic [$clog2(NB_BANKS)-1:0]                                            SCM_TAG_write_dest_int;
   logic [TAG_WIDTH-1:0]                                                   SCM_TAG_write_wdata_int;
   logic [NB_WAYS-1:0]                                                     SCM_TAG_write_way_int;

   // interface with WRITE PORT --> DATA SCM UNIFIED
   logic                                                                   SCM_DATA_write_req_int;
   logic [SCM_DATA_ADDR_WIDTH-1:0]                                         SCM_DATA_write_addr_int;
   logic [$clog2(NB_BANKS)-1:0]                                            SCM_DATA_write_dest_int;
   logic [FETCH_DATA_WIDTH-1:0]                                            SCM_DATA_write_wdata_int;
   logic [NB_WAYS-1:0]                                                     SCM_DATA_write_way_int;



   logic [NB_BANKS-1:0] [NB_CORES:0]                                       TAG_ReadEnable;
   logic [NB_BANKS-1:0] [NB_CORES-1:0]                                     DATA_ReadEnable;
   logic [NB_CORES:0]   [NB_BANKS-1:0][NB_WAYS-1:0] [TAG_WIDTH-1:0]        TAG_ReadData;
   logic [NB_CORES-1:0] [NB_BANKS-1:0][NB_WAYS-1:0] [FETCH_DATA_WIDTH-1:0] DATA_ReadData;

   logic [NB_CORES:0]                                                      notify_refill_done;

   logic [NB_CORES-1:0][NB_WAYS-1:0]                                       fetch_way_int;

   logic [NB_CORES-1:0]                                                    fetch_req_int;
   logic [NB_CORES-1:0][FETCH_ADDR_WIDTH-1:0]                              fetch_addr_int;
   logic [NB_CORES-1:0]                                                    fetch_gnt_int;
   logic [NB_CORES-1:0]                                                    fetch_rvalid_int;
   logic [NB_CORES-1:0][FETCH_DATA_WIDTH-1:0]                              fetch_rdata_int;

   logic [NB_BANKS-1:0]                                                    SCM_TAG_write_dest_OH_int;
   logic [NB_BANKS-1:0]                                                    SCM_DATA_write_dest_OH_int;
   logic [NB_CORES+1:0]                                                    cache_is_bypassed; // NB_CORES+CENTRL_CACHE_CTRL+HW prefetcher

   logic [NB_CORES:0]                                                      retry_fetch;


   logic                                         bypass_icache;
   logic                                         empty_fifo;
   logic                                         flush_icache;
   logic                                         flush_ack;
   logic                                         sel_flush_req;
   logic [FETCH_ADDR_WIDTH-1:0]                  sel_flush_addr;
   logic                                         sel_flush_ack;


   logic [AXI_ID_INT-1:0]                        axi_master_arid_int;
   logic [AXI_ADDR-1:0]                          axi_master_araddr_int;
   logic [ 7:0]                                  axi_master_arlen_int;    
   logic [ 2:0]                                  axi_master_arsize_int;   
   logic [ 1:0]                                  axi_master_arburst_int;  
   logic                                         axi_master_arlock_int;   
   logic [ 3:0]                                  axi_master_arcache_int; 
   logic [ 2:0]                                  axi_master_arprot_int;
   logic [ 3:0]                                  axi_master_arregion_int; 
   logic [ AXI_USER-1:0]                         axi_master_aruser_int;   
   logic [ 3:0]                                  axi_master_arqos_int;    
   logic                                         axi_master_arvalid_int;  
   logic                                         axi_master_arready_int;  


   logic [AXI_ID_INT-1:0]                        axi_master_rid_int;
   logic [AXI_DATA-1:0]                          axi_master_rdata_int;
   logic [1:0]                                   axi_master_rresp_int;
   logic                                         axi_master_rlast_int; 
   logic [AXI_USER-1:0]                          axi_master_ruser_int;
   logic                                         axi_master_rvalid_int;
   logic                                         axi_master_rready_int;


   // Signals from Prefetcher control unit to HW prefetcher Block
   logic               pf_req_to_cc;
   logic [31:0]        pf_addr_to_cc;
   logic               pf_gnt_from_cc;
   logic               pf_rvalid_from_cc;

   // Signal from HW prefetcher to main cache controller
   logic               pf_req_to_master_cc;
   logic [31:0]        pf_addr_to_master_cc;
   logic [NB_WAYS-1:0] pf_way_to_master_cc;
   logic               pf_gnt_from_master_cc;
   logic               pf_rvalid_from_master_cc;




   // Performamce counters
   logic               [31:0]   total_hit_count;
   logic               [31:0]   total_trans_count;
   logic               [31:0]   total_miss_count;

   logic [NB_CORES-1:0][31:0]   bank_hit_count;
   logic [NB_CORES-1:0][31:0]   bank_trans_count;
   logic [NB_CORES-1:0][31:0]   bank_miss_count;

   assign SCM_TAG_write_dest_OH_int  = (1 << SCM_TAG_write_dest_int);
   assign SCM_DATA_write_dest_OH_int = (1 << SCM_DATA_write_dest_int);

   genvar i,j,k,z;
   int unsigned index;


   assign bypass_icache                        = IC_ctrl_unit_slave_if.bypass_req;
   assign IC_ctrl_unit_slave_if.bypass_ack     = cache_is_bypassed;
   assign flush_icache                         = IC_ctrl_unit_slave_if.flush_req;
   assign IC_ctrl_unit_slave_if.flush_ack      = flush_ack;

   assign sel_flush_req                        = IC_ctrl_unit_slave_if.sel_flush_req;
   assign sel_flush_addr                       = IC_ctrl_unit_slave_if.sel_flush_addr;
   assign IC_ctrl_unit_slave_if.sel_flush_ack  = sel_flush_ack;

  // Performamce counters
  if (FEATURE_STAT) begin
    assign IC_ctrl_unit_slave_if.global_hit_count   = total_hit_count;
    assign IC_ctrl_unit_slave_if.global_trans_count = total_trans_count;
    assign IC_ctrl_unit_slave_if.global_miss_count  = total_miss_count;

    always_comb
    begin
        total_hit_count   = '0;
        total_trans_count = '0;
        for (index=0; index<NB_CORES; index++)
        begin
          total_hit_count   = total_hit_count   + bank_hit_count[index];
          total_trans_count = total_trans_count + bank_trans_count[index];

          IC_ctrl_unit_slave_if.bank_hit_count   [index]  = bank_hit_count   [index];
          IC_ctrl_unit_slave_if.bank_trans_count [index]  = bank_trans_count [index];
          IC_ctrl_unit_slave_if.bank_miss_count  [index]  = bank_miss_count  [index];
        end
    end

    always_ff @(posedge clk, negedge rst_n)
    begin
        if(~rst_n)
        begin
            total_miss_count <= 0;
        end
        else
        begin
          if(IC_ctrl_unit_slave_if.ctrl_clear_regs)
            total_miss_count <= '0;
          else  if(IC_ctrl_unit_slave_if.ctrl_enable_regs & axi_master_arvalid_int & axi_master_arready_int )
                      total_miss_count <= total_miss_count + 1'b1;
        end
    end
  end

   ///////////////////////////////////////////////////////////////////////////////
   // ██████╗ ██████╗ ██╗██╗   ██╗ █████╗ ████████╗███████╗     ██████╗ ██████╗ //
   // ██╔══██╗██╔══██╗██║██║   ██║██╔══██╗╚══██╔══╝██╔════╝    ██╔════╝██╔════╝ //
   // ██████╔╝██████╔╝██║██║   ██║███████║   ██║   █████╗      ██║     ██║      //
   // ██╔═══╝ ██╔══██╗██║╚██╗ ██╔╝██╔══██║   ██║   ██╔══╝      ██║     ██║      //
   // ██║     ██║  ██║██║ ╚████╔╝ ██║  ██║   ██║   ███████╗    ╚██████╗╚██████╗ //
   // ╚═╝     ╚═╝  ╚═╝╚═╝  ╚═══╝  ╚═╝  ╚═╝   ╚═╝   ╚══════╝     ╚═════╝ ╚═════╝ //
   /////////////////////////////////////////////////////////////////////////////// 
   generate
      for(i=0; i<NB_CORES; i++)
      begin : ICACHE_BANK
         icache_bank_mp_128
         #(
            .FETCH_ADDR_WIDTH     ( FETCH_ADDR_WIDTH     ),
            .FETCH_DATA_WIDTH     ( FETCH_DATA_WIDTH     ),

            .NB_CORES             ( NB_CORES+1           ),
            .BANK_ID              ( i                    ),
            .NB_BANKS             ( NB_BANKS             ),
            .NB_WAYS              ( NB_WAYS              ),
            .CACHE_LINE           ( CACHE_LINE           ),

            .SCM_ADDR_WIDTH       ( SCM_TAG_ADDR_WIDTH   ),
            .SCM_TAG_WIDTH        ( TAG_WIDTH            ),
            .SCM_DATA_WIDTH       ( FETCH_DATA_WIDTH     ),

            .SET_ID_LSB           ( SET_ID_LSB           ),
            .SET_ID_MSB           ( SET_ID_MSB           ),
            .TAG_LSB              ( TAG_LSB              ), 
            .TAG_MSB              ( TAG_MSB              ),

            .AXI_ID               ( AXI_ID               ),
            .AXI_ADDR             ( AXI_ADDR             ),
            .AXI_USER             ( AXI_USER             ),
            .AXI_DATA             ( AXI_DATA             )
         )
         icache_bank_i
         (
            .clk                        ( clk                                      ),
            .rst_n                      ( rst_n                                    ),
            .bypass_icache_i            ( bypass_icache                            ),
            .cache_is_bypassed_o        ( cache_is_bypassed[i]                     ),
            .bypass_status_i            ( cache_is_bypassed                        ),
            .test_en_i                  ( test_en_i                                ),

            .notify_refill_done_i       ( notify_refill_done[i]                    ),
            .empty_fifo_i               ( empty_fifo                               ),
            .retry_fetch_i              ( retry_fetch[i]                           ),

            // interface with processor
            .fetch_req_i                ( fetch_req_i[i]                           ),
            .fetch_addr_i               ( fetch_addr_i[i]                          ),
            .fetch_gnt_o                ( fetch_gnt_o[i]                           ),
            .fetch_rvalid_o             ( fetch_rvalid_o[i]                        ),
            .fetch_rdata_o              ( fetch_rdata_o[i]                         ),

            // interface with READ PORT --> SCM DATA
            .DATA_read_req_o            ( DATA_read_req_int[i]                     ),      
            .DATA_read_addr_o           ( DATA_read_addr_int[i]                    ),
            .DATA_read_rdata_i          ( DATA_ReadData[i]                         ),

            // interface with READ PORT --> SCM TAG
            .TAG_read_req_o             ( TAG_read_req_int[i]                      ),       
            .TAG_read_addr_o            ( TAG_read_addr_int[i]                     ),
            .TAG_read_rdata_i           ( TAG_ReadData[i]                          ),

            // interface to CC to AXI bridge
            .fetch_req_o                ( fetch_req_int[i]                         ),
            .fetch_addr_o               ( fetch_addr_int[i]                        ),
            .fetch_way_o                ( fetch_way_int[i]                         ),
           
            .fetch_gnt_i                ( fetch_gnt_int[i]                         ),
            .fetch_rvalid_i             ( fetch_rvalid_int[i]                      ),
            .fetch_rdata_i              ( fetch_rdata_int[i]                       ),
            .ctrl_hit_count_icache_o    ( bank_hit_count[i]                        ),
            .ctrl_trans_count_icache_o  ( bank_trans_count[i]                      ),
            .ctrl_miss_count_icache_o   ( bank_miss_count[i]                       ),
            .ctrl_clear_regs_icache_i   ( IC_ctrl_unit_slave_if.ctrl_clear_regs    ),
            .ctrl_enable_regs_icache_i  ( IC_ctrl_unit_slave_if.ctrl_enable_regs   )
         );
      end

   


      for(i=0;i<NB_BANKS;i++)
      begin
         for(j=0;j<NB_CORES+1;j++)
         begin
            assign TAG_ReadEnable[i][j]  = TAG_read_req_int[j][i];
         end
      end

      for(i=0;i<NB_BANKS;i++)
      begin
         for(j=0;j<NB_CORES;j++)
         begin
            assign DATA_ReadEnable[i][j] = DATA_read_req_int[j][i];
         end
      end


         for(i=0;i<NB_BANKS;i++)
         begin
            for(j=0;j<NB_WAYS;j++)
            begin
                for(k=0;k<NB_CORES+1;k++)
                begin
                   assign TAG_ReadData[k][i][j] = TAG_read_rdata_int[i][j][k];
                end
            end
         end

         for(i=0;i<NB_BANKS;i++)
         begin
            for(j=0;j<NB_WAYS;j++)
            begin
                for(k=0;k<NB_CORES;k++)
                begin
                   assign DATA_ReadData[k][i][j] = DATA_read_rdata_int[i][j][k];
                end
            end
         end



   //////////////////////////////////////////////////////////////////////////////
   // ████████╗ █████╗  ██████╗     ██████╗  █████╗ ███╗   ██╗██╗  ██╗███████╗ //
   // ╚══██╔══╝██╔══██╗██╔════╝     ██╔══██╗██╔══██╗████╗  ██║██║ ██╔╝██╔════╝ //
   //    ██║   ███████║██║  ███╗    ██████╔╝███████║██╔██╗ ██║█████╔╝ ███████╗ //
   //    ██║   ██╔══██║██║   ██║    ██╔══██╗██╔══██║██║╚██╗██║██╔═██╗ ╚════██║ //
   //    ██║   ██║  ██║╚██████╔╝    ██████╔╝██║  ██║██║ ╚████║██║  ██╗███████║ //
   //    ╚═╝   ╚═╝  ╚═╝ ╚═════╝     ╚═════╝ ╚═╝  ╚═╝╚═╝  ╚═══╝╚═╝  ╚═╝╚══════╝ //
   //////////////////////////////////////////////////////////////////////////////

      for(i=0; i<NB_BANKS; i++)
      begin : _TAG_BANKS_
         for(j=0; j<NB_WAYS; j++)
         begin : _TAG_WAY_
               register_file_1w_multi_port_read
               #(
                   .ADDR_WIDTH    ( SCM_TAG_ADDR_WIDTH  ),
                   .DATA_WIDTH    ( TAG_WIDTH       ),
                   .N_READ        ( NB_CORES+1      ),
                   .N_WRITE       ( 1               )
               )
               TAG_BANK
               (
                   .clk         (clk                ),
                   .rst_n       ( rst_n             ),
                   .test_en_i   (test_en_i          ),

                   .ReadEnable  (TAG_ReadEnable[i]  ),
                   .ReadAddr    (TAG_read_addr_int  ),
                   .ReadData    (TAG_read_rdata_int[i][j] ),

                   .WriteEnable (SCM_TAG_write_req_int & SCM_TAG_write_way_int[j] & SCM_TAG_write_dest_OH_int[i] ),
                   .WriteAddr   (SCM_TAG_write_addr_int                                                          ),
                   .WriteData   (SCM_TAG_write_wdata_int                                                         )
               );
         end
      end

   /////////////////////////////////////////////////////////////////////////////////////
   // ██████╗  █████╗ ████████╗ █████╗     ██████╗  █████╗ ███╗   ██╗██╗  ██╗███████╗ //
   // ██╔══██╗██╔══██╗╚══██╔══╝██╔══██╗    ██╔══██╗██╔══██╗████╗  ██║██║ ██╔╝██╔════╝ //
   // ██║  ██║███████║   ██║   ███████║    ██████╔╝███████║██╔██╗ ██║█████╔╝ ███████╗ //
   // ██║  ██║██╔══██║   ██║   ██╔══██║    ██╔══██╗██╔══██║██║╚██╗██║██╔═██╗ ╚════██║ //
   // ██████╔╝██║  ██║   ██║   ██║  ██║    ██████╔╝██║  ██║██║ ╚████║██║  ██╗███████║ //
   // ╚═════╝ ╚═╝  ╚═╝   ╚═╝   ╚═╝  ╚═╝    ╚═════╝ ╚═╝  ╚═╝╚═╝  ╚═══╝╚═╝  ╚═╝╚══════╝ //
   /////////////////////////////////////////////////////////////////////////////////////                                                                            

      for(i=0; i<NB_BANKS; i++)
      begin : _DATA_BANKS_
         for(j=0; j<NB_WAYS; j++)
         begin : _DATA_WAY_
               register_file_1w_multi_port_read
               #(
                   .ADDR_WIDTH   ( SCM_DATA_ADDR_WIDTH   ), //= 5,
                   .DATA_WIDTH   ( FETCH_DATA_WIDTH      ), //= 128
                   .N_READ       ( NB_CORES              ),
                   .N_WRITE      ( 1                     ) 
               )
               DATA_BANK
               (
                   .clk         ( clk                    ),
                   .rst_n       ( rst_n                  ),
                   .test_en_i   ( test_en_i              ),

                   .ReadEnable  ( DATA_ReadEnable[i]     ),
                   .ReadAddr    ( DATA_read_addr_int     ),
                   .ReadData    ( DATA_read_rdata_int[i][j] ),

                   .WriteEnable ( SCM_DATA_write_req_int & SCM_DATA_write_way_int[j] & SCM_DATA_write_dest_OH_int[i] ),
                   .WriteAddr   ( SCM_DATA_write_addr_int                                                            ),
                   .WriteData   ( SCM_DATA_write_wdata_int                                                           )
               );
         end
      end

   endgenerate









   // Main Cache controller:
   // It collects request form private cache controllers and HW prefetcher
   // And handles  merging and request refills

   //////////////////////////////////////////////////////////  
   // ███╗   ███╗ █████╗ ██╗███╗   ██╗     ██████╗ ██████╗ //
   // ████╗ ████║██╔══██╗██║████╗  ██║    ██╔════╝██╔════╝ //
   // ██╔████╔██║███████║██║██╔██╗ ██║    ██║     ██║      //
   // ██║╚██╔╝██║██╔══██║██║██║╚██╗██║    ██║     ██║      //
   // ██║ ╚═╝ ██║██║  ██║██║██║ ╚████║    ╚██████╗╚██████╗ //
   // ╚═╝     ╚═╝╚═╝  ╚═╝╚═╝╚═╝  ╚═══╝     ╚═════╝ ╚═════╝ //
   //////////////////////////////////////////////////////////

   cache_controller_to_axi_128_PF
   #(
      .FETCH_ADDR_WIDTH      ( FETCH_ADDR_WIDTH     ),// = 32,
      .FETCH_DATA_WIDTH      ( FETCH_DATA_WIDTH     ),// = 32,

      .NB_CORES              ( NB_CORES             ),// = 4,
      .NB_BANKS              ( NB_BANKS             ),// = 4,
      .NB_WAYS               ( NB_WAYS              ),// = 4,
      
      .SCM_TAG_WIDTH         ( TAG_WIDTH            ),// = 6,
      .SCM_DATA_WIDTH        ( FETCH_DATA_WIDTH     ),// = 64,

      .SCM_ADDR_WIDTH        ( SCM_TAG_ADDR_WIDTH   ),// = 16,
      .SET_ID_LSB            ( SET_ID_LSB           ),// = 6,
      .SET_ID_MSB            ( SET_ID_MSB           ),// = SET_ID_LSB+SCM_ADDR_WIDTH-1,
      .TAG_LSB               ( TAG_LSB              ),// = SET_ID_MSB + 1,
      .TAG_MSB               ( TAG_MSB              ),// = TAG_LSB + SCM_TAG_WIDTH - 2,  //1 bit is count for valid

      .AXI_ID                ( AXI_ID_INT           ),// = 4,
      .AXI_ADDR              ( AXI_ADDR             ),// = 32,
      .AXI_USER              ( AXI_USER             ),// = 6,
      .AXI_DATA              ( AXI_DATA             )// = 64
   )
   u_cache_controller_to_axi
   (
      .clk                   ( clk                              ),
      .rst_n                 ( rst_n                            ),
      .test_en_i             ( test_en_i                        ),

      .bypass_icache_i       ( bypass_icache                    ),
      .notify_refill_done_o  ( notify_refill_done               ),
      .cache_bypassed_o      ( cache_is_bypassed[NB_CORES+1]    ),
      .bypass_status_i       ( cache_is_bypassed[NB_CORES:0]    ),
      .empty_fifo_o          ( empty_fifo                       ),
      .retry_fetch_o         ( retry_fetch                      ),
      .flush_icache_i        ( flush_icache                     ),
      .flush_ack_o           ( flush_ack                        ),
      
      .sel_flush_req_i       ( sel_flush_req                    ),
      .sel_flush_addr_i      ( sel_flush_addr                   ),
      .sel_flush_ack_o       ( sel_flush_ack                    ),

      // interface with processor
      .fetch_req_i           ( fetch_req_int                    ),
      .fetch_addr_i          ( fetch_addr_int                   ),
      .fetch_way_i           ( fetch_way_int                    ),
      .fetch_gnt_o           ( fetch_gnt_int                    ),
      .fetch_rvalid_o        ( fetch_rvalid_int                 ),
      .fetch_rdata_o         ( fetch_rdata_int                  ),

      // Interface with Prefetcher
      .pf_fetch_req_i        (  pf_req_to_master_cc             ),       
      .pf_fetch_addr_i       (  pf_addr_to_master_cc            ),       
      .pf_fetch_way_i        (  pf_way_to_master_cc             ),       
      .pf_fetch_gnt_o        (  pf_gnt_from_master_cc           ),       
      .pf_fetch_rvalid_o     (  pf_rvalid_from_master_cc        ),



      // interface with WRITE PORT --> TAG SCM Unified PORT
      .SCM_TAG_write_req_o   ( SCM_TAG_write_req_int            ),   
      .SCM_TAG_write_addr_o  ( SCM_TAG_write_addr_int           ),
      .SCM_TAG_write_dest_o  ( SCM_TAG_write_dest_int           ),
      .SCM_TAG_write_wdata_o ( SCM_TAG_write_wdata_int          ),
      .SCM_TAG_write_way_o   ( SCM_TAG_write_way_int            ),  

      // interface with WRITE PORT --> DATA SCM Unified PORT
      .SCM_DATA_write_req_o  ( SCM_DATA_write_req_int           ),   
      .SCM_DATA_write_addr_o ( SCM_DATA_write_addr_int          ), // double number of rows with respect TAG SCM ARRAY
      .SCM_DATA_write_dest_o ( SCM_DATA_write_dest_int          ),
      .SCM_DATA_write_wdata_o( SCM_DATA_write_wdata_int         ),
      .SCM_DATA_write_way_o  ( SCM_DATA_write_way_int           ),  

      //AXI read address bus -------------------------------------------
      .axi_master_arid_o     ( axi_master_arid_int[AXI_ID_INT-1:0] ),
      .axi_master_araddr_o   ( axi_master_araddr_int               ),
      .axi_master_arlen_o    ( axi_master_arlen_int                ),
      .axi_master_arsize_o   ( axi_master_arsize_int               ),
      .axi_master_arburst_o  ( axi_master_arburst_int              ),
      .axi_master_arlock_o   ( axi_master_arlock_int               ),
      .axi_master_arcache_o  ( axi_master_arcache_int              ), 
      .axi_master_arprot_o   ( axi_master_arprot_int               ),
      .axi_master_arregion_o ( axi_master_arregion_int             ),
      .axi_master_aruser_o   ( axi_master_aruser_int               ),
      .axi_master_arqos_o    ( axi_master_arqos_int                ),
      .axi_master_arvalid_o  ( axi_master_arvalid_int              ),
      .axi_master_arready_i  ( axi_master_arready_int              ),
      // ---------------------------------------------------------------


      //AXI BACKWARD read data bus ----------------------------------------------
      .axi_master_rid_i      ( axi_master_rid_int[AXI_ID_INT-1:0]  ),
      .axi_master_rdata_i    ( axi_master_rdata_int               ),
      .axi_master_rresp_i    ( axi_master_rresp_int               ),
      .axi_master_rlast_i    ( axi_master_rlast_int               ),
      .axi_master_ruser_i    ( axi_master_ruser_int               ),
      .axi_master_rvalid_i   ( axi_master_rvalid_int              ),
      .axi_master_rready_o   ( axi_master_rready_int              )
   );



   // Axi Write Channels tied to 0

   assign axi_master_arid_o[AXI_ID-1:AXI_ID_INT] = '0;

   assign axi_master_awid_o     = '0;
   assign axi_master_awaddr_o   = '0;             
   assign axi_master_awlen_o    = '0;             
   assign axi_master_awsize_o   = '0;             
   assign axi_master_awburst_o  = '0;             
   assign axi_master_awlock_o   = '0;             
   assign axi_master_awcache_o  = '0;             
   assign axi_master_awprot_o   = '0;             
   assign axi_master_awregion_o = '0;             
   assign axi_master_awuser_o   = '0;             
   assign axi_master_awqos_o    = '0;             
   assign axi_master_awvalid_o  = '0;                          
   assign axi_master_wdata_o    = '0;             
   assign axi_master_wstrb_o    = '0;             
   assign axi_master_wlast_o    = '0;             
   assign axi_master_wuser_o    = '0;             
   assign axi_master_wvalid_o   = '0;               
   assign axi_master_bready_o   = '0;             


`ifdef USE_AXI_SLICES

   ////////////////////////////////////////////////////////////////////////
   //  █████╗ ██╗  ██╗██╗    ███████╗██╗     ██╗ ██████╗███████╗███████╗ //
   // ██╔══██╗╚██╗██╔╝██║    ██╔════╝██║     ██║██╔════╝██╔════╝██╔════╝ //
   // ███████║ ╚███╔╝ ██║    ███████╗██║     ██║██║     █████╗  ███████╗ //
   // ██╔══██║ ██╔██╗ ██║    ╚════██║██║     ██║██║     ██╔══╝  ╚════██║ //
   // ██║  ██║██╔╝ ██╗██║    ███████║███████╗██║╚██████╗███████╗███████║ //
   // ╚═╝  ╚═╝╚═╝  ╚═╝╚═╝    ╚══════╝╚══════╝╚═╝ ╚═════╝╚══════╝╚══════╝ //
   ////////////////////////////////////////////////////////////////////////
   // to alleviate pressure on AXI side, this SLice can be added or not
   // by defining the USE_AXI_SLICES macro. It will insert a AR and R slice on the AXI plug
   axi_ar_buffer
   #(
      .ID_WIDTH     ( AXI_ID_INT  ), 
      .ADDR_WIDTH   ( AXI_ADDR    ),
      .USER_WIDTH   ( AXI_USER    ),
      .BUFFER_DEPTH ( 2           )
   )
   i_AXI_AR_BUFFER
   (
      .clk_i           ( clk                                 ),
      .rst_ni          ( rst_n                               ),
      .test_en_i       ( test_en_i                           ),

      .slave_valid_i   ( axi_master_arvalid_int              ),
      .slave_addr_i    ( axi_master_araddr_int               ),
      .slave_prot_i    ( axi_master_arprot_int               ),
      .slave_region_i  ( axi_master_arregion_int             ),
      .slave_len_i     ( axi_master_arlen_int                ),
      .slave_size_i    ( axi_master_arsize_int               ),
      .slave_burst_i   ( axi_master_arburst_int              ),
      .slave_lock_i    ( axi_master_arlock_int               ),
      .slave_cache_i   ( axi_master_arcache_int              ),
      .slave_qos_i     ( axi_master_arqos_int                ),
      .slave_id_i      ( axi_master_arid_int[AXI_ID_INT-1:0] ),
      .slave_user_i    ( axi_master_aruser_int               ),
      .slave_ready_o   ( axi_master_arready_int              ),

      .master_valid_o  ( axi_master_arvalid_o                ),
      .master_addr_o   ( axi_master_araddr_o                 ),
      .master_prot_o   ( axi_master_arprot_o                 ),
      .master_region_o ( axi_master_arregion_o               ),
      .master_len_o    ( axi_master_arlen_o                  ),
      .master_size_o   ( axi_master_arsize_o                 ),
      .master_burst_o  ( axi_master_arburst_o                ),
      .master_lock_o   ( axi_master_arlock_o                 ),
      .master_cache_o  ( axi_master_arcache_o                ),
      .master_qos_o    ( axi_master_arqos_o                  ),
      .master_id_o     ( axi_master_arid_o[AXI_ID_INT-1:0]   ),
      .master_user_o   ( axi_master_aruser_o                 ),
      .master_ready_i  ( axi_master_arready_i                )
   );

   axi_r_buffer
      #(
      .ID_WIDTH       ( AXI_ID_INT                         ),
      .DATA_WIDTH     ( AXI_DATA                           ),
      .USER_WIDTH     ( AXI_USER                           ),
      .BUFFER_DEPTH   ( 2                                  )
   )
   i_AXI_R_BUFFER
   (
      .clk_i          ( clk                                ),
      .rst_ni         ( rst_n                              ),
      .test_en_i      ( test_en_i                          ),

      .slave_valid_i  ( axi_master_rvalid_i                ),
      .slave_data_i   ( axi_master_rdata_i                 ),
      .slave_resp_i   ( axi_master_rresp_i                 ),
      .slave_user_i   ( axi_master_ruser_i                 ),
      .slave_id_i     ( axi_master_rid_i[AXI_ID_INT-1:0]   ),
      .slave_last_i   ( axi_master_rlast_i                 ),
      .slave_ready_o  ( axi_master_rready_o                ),

      .master_valid_o ( axi_master_rvalid_int              ),
      .master_data_o  ( axi_master_rdata_int               ),
      .master_resp_o  ( axi_master_rresp_int               ),
      .master_user_o  ( axi_master_ruser_int               ),
      .master_id_o    ( axi_master_rid_int[AXI_ID_INT-1:0]  ),
      .master_last_o  ( axi_master_rlast_int               ),
      .master_ready_i ( axi_master_rready_int              )
);

`else 
   assign axi_master_rvalid_int               = axi_master_rvalid_i                ;
   assign axi_master_rdata_int                = axi_master_rdata_i                 ;
   assign axi_master_rresp_int                = axi_master_rresp_i                 ;
   assign axi_master_ruser_int                = axi_master_ruser_i                 ;
   assign axi_master_rid_int[AXI_ID_INT-1:0]  = axi_master_rid_i[AXI_ID_INT-1:0]   ;
   assign axi_master_rlast_int                = axi_master_rlast_i                 ;
   assign axi_master_rready_o                 = axi_master_rready_int              ;

   assign axi_master_arvalid_o                = axi_master_arvalid_int              ;
   assign axi_master_araddr_o                 = axi_master_araddr_int               ;
   assign axi_master_arprot_o                 = axi_master_arprot_int               ;
   assign axi_master_arregion_o               = axi_master_arregion_int             ;
   assign axi_master_arlen_o                  = axi_master_arlen_int                ;
   assign axi_master_arsize_o                 = axi_master_arsize_int               ;
   assign axi_master_arburst_o                = axi_master_arburst_int              ;
   assign axi_master_arlock_o                 = axi_master_arlock_int               ;
   assign axi_master_arcache_o                = axi_master_arcache_int              ;
   assign axi_master_arqos_o                  = axi_master_arqos_int                ;
   assign axi_master_arid_o[AXI_ID_INT-1:0]   = axi_master_arid_int[AXI_ID_INT-1:0] ;
   assign axi_master_aruser_o                 = axi_master_aruser_int               ;
   assign axi_master_arready_int              = axi_master_arready_i                ;
`endif



   ///////////////////////////////////////////////////////////////////////////////////////////////////////////
   // ██████╗ ██████╗ ███████╗███████╗███████╗████████╗ ██████╗██╗  ██╗███████╗██████╗      ██████╗ ██████╗ //
   // ██╔══██╗██╔══██╗██╔════╝██╔════╝██╔════╝╚══██╔══╝██╔════╝██║  ██║██╔════╝██╔══██╗    ██╔════╝██╔════╝ //
   // ██████╔╝██████╔╝█████╗  █████╗  █████╗     ██║   ██║     ███████║█████╗  ██████╔╝    ██║     ██║      //
   // ██╔═══╝ ██╔══██╗██╔══╝  ██╔══╝  ██╔══╝     ██║   ██║     ██╔══██║██╔══╝  ██╔══██╗    ██║     ██║      //
   // ██║     ██║  ██║███████╗██║     ███████╗   ██║   ╚██████╗██║  ██║███████╗██║  ██║    ╚██████╗╚██████╗ //
   // ╚═╝     ╚═╝  ╚═╝╚══════╝╚═╝     ╚══════╝   ╚═╝    ╚═════╝╚═╝  ╚═╝╚══════╝╚═╝  ╚═╝     ╚═════╝ ╚═════╝ //
   ///////////////////////////////////////////////////////////////////////////////////////////////////////////

   icache_bank_mp_128_PF
   #(
      .FETCH_ADDR_WIDTH     ( FETCH_ADDR_WIDTH     ),
      .FETCH_DATA_WIDTH     ( FETCH_DATA_WIDTH     ),

      .NB_CORES             ( NB_CORES+1           ),
      .BANK_ID              ( NB_CORES             ),
      .NB_BANKS             ( NB_BANKS             ),
      .NB_WAYS              ( NB_WAYS              ),
      .CACHE_LINE           ( CACHE_LINE           ),

      .SCM_ADDR_WIDTH       ( SCM_TAG_ADDR_WIDTH   ),
      .SCM_TAG_WIDTH        ( TAG_WIDTH            ),
      .SCM_DATA_WIDTH       ( FETCH_DATA_WIDTH     ),

      .SET_ID_LSB           ( SET_ID_LSB           ),
      .SET_ID_MSB           ( SET_ID_MSB           ),
      .TAG_LSB              ( TAG_LSB              ), 
      .TAG_MSB              ( TAG_MSB              ),

      .AXI_ID               ( AXI_ID               ),
      .AXI_ADDR             ( AXI_ADDR             ),
      .AXI_USER             ( AXI_USER             ),
      .AXI_DATA             ( AXI_DATA             )
   )
   pf_cc
   (
      .clk                  ( clk                           ),
      .rst_n                ( rst_n                         ),
      .test_en_i            ( test_en_i                     ),

      .notify_refill_done_i ( notify_refill_done[NB_CORES] ),
      .bypass_icache_i      ( bypass_icache                ),
      .empty_fifo_i         ( empty_fifo                   ),
      .cache_is_bypassed_o  ( cache_is_bypassed[NB_CORES]  ),
      .bypass_status_i      ( cache_is_bypassed            ),
      .retry_fetch_i        ( retry_fetch[NB_CORES]        ),


      .fetch_req_i          ( pf_req_to_cc                 ),
      .fetch_addr_i         ( pf_addr_to_cc                ),
      .fetch_gnt_o          ( pf_gnt_from_cc               ),
      .fetch_rvalid_o       ( pf_rvalid_from_cc            ),

      .TAG_read_req_o       ( TAG_read_req_int[NB_CORES]   ),   
      .TAG_read_addr_o      ( TAG_read_addr_int[NB_CORES]  ),
      .TAG_read_rdata_i     ( TAG_ReadData[NB_CORES]       ),


      // To be multiplexed at the output of the XBAR_ICACHE
      .fetch_req_o          (  pf_req_to_master_cc         ),
      .fetch_addr_o         (  pf_addr_to_master_cc        ),
      .fetch_way_o          (  pf_way_to_master_cc         ),  
      .fetch_gnt_i          (  pf_gnt_from_master_cc       ),
      .fetch_rvalid_i       (  pf_rvalid_from_master_cc    )
   );


   /////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // ██╗  ██╗██╗    ██╗    ██████╗ ██████╗ ███████╗███████╗███████╗████████╗ ██████╗██╗  ██╗███████╗██████╗  //
   // ██║  ██║██║    ██║    ██╔══██╗██╔══██╗██╔════╝██╔════╝██╔════╝╚══██╔══╝██╔════╝██║  ██║██╔════╝██╔══██╗ //
   // ███████║██║ █╗ ██║    ██████╔╝██████╔╝█████╗  █████╗  █████╗     ██║   ██║     ███████║█████╗  ██████╔╝ //
   // ██╔══██║██║███╗██║    ██╔═══╝ ██╔══██╗██╔══╝  ██╔══╝  ██╔══╝     ██║   ██║     ██╔══██║██╔══╝  ██╔══██╗ //
   // ██║  ██║╚███╔███╔╝    ██║     ██║  ██║███████╗██║     ███████╗   ██║   ╚██████╗██║  ██║███████╗██║  ██║ //
   // ╚═╝  ╚═╝ ╚══╝╚══╝     ╚═╝     ╚═╝  ╚═╝╚══════╝╚═╝     ╚══════╝   ╚═╝    ╚═════╝╚═╝  ╚═╝╚══════╝╚═╝  ╚═╝ //
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////

   prefetcher_if sw_prefetcher_if
   (
      .clk         ( clk       ),
      .rst_n       ( rst_n     ),
      .test_en_i   ( test_en_i ),


      .pf_addr_i   ( IC_ctrl_unit_slave_if.pf_addr ),
      .pf_size_i   ( IC_ctrl_unit_slave_if.pf_size ),
      .pf_req_i    ( IC_ctrl_unit_slave_if.pf_req  ),
      .pf_ack_o    ( IC_ctrl_unit_slave_if.pf_ack  ),
      .pf_done_o   ( IC_ctrl_unit_slave_if.pf_done ),


      .pf_req_o    ( pf_req_to_cc      ),
      .pf_addr_o   ( pf_addr_to_cc     ),
      .pf_gnt_i    ( pf_gnt_from_cc    ),
      .pf_rvalid_i ( pf_rvalid_from_cc )
   );
endmodule // icache_top_scm_mp
