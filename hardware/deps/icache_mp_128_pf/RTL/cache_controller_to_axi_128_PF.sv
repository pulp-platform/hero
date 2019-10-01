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
// Module Name:    cache_controller_to_axi_128_PF                             //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    This block represents private cache controller that        //
//                 receives the requests  from the Prefetcher unit            //
//                 and perform TAG access for TAG hit check. In case of MISS  //
//                 the refill is forwarded to the main cache controller (TOP) //
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



module cache_controller_to_axi_128_PF
#(
   parameter FETCH_ADDR_WIDTH = 32,
   parameter FETCH_DATA_WIDTH = 128,

   parameter NB_CORES        = 8,
   parameter NB_BANKS        = 8,
   parameter NB_WAYS         = 4,
   
   parameter SCM_TAG_WIDTH   = 6,
   parameter SCM_DATA_WIDTH  = 128,

   parameter SCM_ADDR_WIDTH  = 16,
   parameter SET_ID_LSB      = 6,
   parameter SET_ID_MSB      = SET_ID_LSB+SCM_ADDR_WIDTH-1,
   parameter TAG_LSB         = SET_ID_MSB + 1,
   parameter TAG_MSB         = TAG_LSB + SCM_TAG_WIDTH - 2,  //1 bit is count for valid

   parameter AXI_ID          = $clog2(NB_CORES+1),
   parameter AXI_ADDR        = 32,
   parameter AXI_USER        = 6,
   parameter AXI_DATA        = 64
)   
(
   input  logic                                        clk,
   input  logic                                        rst_n,
   input  logic                                        test_en_i,

   input  logic                                        bypass_icache_i,
   output logic [NB_CORES:0]                           notify_refill_done_o,
   output logic                                        cache_bypassed_o,
   input  logic [NB_CORES:0]                           bypass_status_i,

   input  logic                                        flush_icache_i,
   output logic                                        flush_ack_o,

   input  logic                                        sel_flush_req_i ,
   input  logic [FETCH_ADDR_WIDTH-1:0]                 sel_flush_addr_i,
   output logic                                        sel_flush_ack_o ,


   output logic                                        empty_fifo_o,
   output logic [NB_CORES:0]                           retry_fetch_o,

   // interface with processor
   input  logic [NB_CORES-1:0]                         fetch_req_i,
   input  logic [NB_CORES-1:0][FETCH_ADDR_WIDTH-1:0]   fetch_addr_i,
   input  logic [NB_CORES-1:0][NB_WAYS-1:0]            fetch_way_i,

   output logic [NB_CORES-1:0]                         fetch_gnt_o,
   output logic [NB_CORES-1:0]                         fetch_rvalid_o,
   output logic [NB_CORES-1:0][FETCH_DATA_WIDTH-1:0]   fetch_rdata_o,

   input  logic                                        pf_fetch_req_i,
   input  logic [FETCH_ADDR_WIDTH-1:0]                 pf_fetch_addr_i,
   input  logic [NB_WAYS-1:0]                          pf_fetch_way_i,
   output logic                                        pf_fetch_gnt_o,
   output logic                                        pf_fetch_rvalid_o,




   // interface with WRITE PORT --> TAG SCM Unified PORT
   output logic                                        SCM_TAG_write_req_o,   
   output logic [SCM_ADDR_WIDTH-1:0]                   SCM_TAG_write_addr_o,
   output logic [$clog2(NB_BANKS)-1:0]                 SCM_TAG_write_dest_o,
   output logic [SCM_TAG_WIDTH-1:0]                    SCM_TAG_write_wdata_o,
   output logic [NB_WAYS-1:0]                          SCM_TAG_write_way_o,  

   // interface with WRITE PORT --> DATA SCM Unified PORT
   output logic                                        SCM_DATA_write_req_o,   
   output logic [SCM_ADDR_WIDTH-1:0]                   SCM_DATA_write_addr_o, // double number of rows with respect TAG SCM ARRAY
   output logic [$clog2(NB_BANKS)-1:0]                 SCM_DATA_write_dest_o,
   output logic [SCM_DATA_WIDTH-1:0]                   SCM_DATA_write_wdata_o,
   output logic [NB_WAYS-1:0]                          SCM_DATA_write_way_o,  

   //AXI read address bus -------------------------------------------
   output  logic [AXI_ID-1:0]                          axi_master_arid_o,
   output  logic [AXI_ADDR-1:0]                        axi_master_araddr_o,
   output  logic [7:0]                                 axi_master_arlen_o,    //burst length - 1 to 16
   output  logic [2:0]                                 axi_master_arsize_o,   //size of each transfer in burst
   output  logic [1:0]                                 axi_master_arburst_o,  //for bursts>1, accept only incr burst=01
   output  logic                                       axi_master_arlock_o,   //only normal access supported axs_awlock=00
   output  logic [3:0]                                 axi_master_arcache_o, 
   output  logic [2:0]                                 axi_master_arprot_o,
   output  logic [3:0]                                 axi_master_arregion_o, //
   output  logic [AXI_USER-1:0]                        axi_master_aruser_o,   //
   output  logic [3:0]                                 axi_master_arqos_o,    //  
   output  logic                                       axi_master_arvalid_o,  //master addr valid
   input   logic                                       axi_master_arready_i,  //slave ready to accept
   // ---------------------------------------------------------------


   //AXI BACKWARD read data bus ----------------------------------------------
   input  logic [AXI_ID-1:0]                           axi_master_rid_i,
   input  logic [AXI_DATA-1:0]                         axi_master_rdata_i,
   input  logic [1:0]                                  axi_master_rresp_i,
   input  logic                                        axi_master_rlast_i,    //last transfer in burst
   input  logic [AXI_USER-1:0]                         axi_master_ruser_i,
   input  logic                                        axi_master_rvalid_i,   //slave data valid
   output logic                                        axi_master_rready_o    //master ready to accept
);

   localparam  DEPTH          = NB_CORES;
   localparam  LOG2_DEPTH     = $clog2(DEPTH);

   // FSM State declaration
   enum logic {IDLE_COMP, DISP_COMP }                  CS_COMP, NS_COMP;

   // interface with CTRL WRITE PORT --> SCM DATA
   logic                                               ctrl_SCM_write_req;   
   logic [$clog2(NB_BANKS)-1:0]                        ctrl_SCM_write_dest;
   logic [SCM_ADDR_WIDTH-1:0]                          ctrl_SCM_write_addr;
   logic [SCM_TAG_WIDTH-1:0]                           ctrl_SCM_write_wdata;
   logic [NB_WAYS-1:0]                                 ctrl_SCM_write_way;

   // interface with REFILL WRITE PORT --> SCM DATA
   logic                                               refill_TAG_SCM_write_req;   
   logic [$clog2(NB_BANKS)-1:0]                        refill_TAG_SCM_write_dest;
   logic [SCM_ADDR_WIDTH-1:0]                          refill_TAG_SCM_write_addr;
   logic [SCM_TAG_WIDTH-1:0]                           refill_TAG_SCM_write_wdata;
   logic [NB_WAYS-1:0]                                 refill_TAG_SCM_write_way;

   // interface with REFILL WRITE PORT --> SCM DATA
   logic                                               refill_DATA_SCM_write_req;   
   logic [$clog2(NB_BANKS)-1:0]                        refill_DATA_SCM_write_dest;
   logic [SCM_ADDR_WIDTH:0]                            refill_DATA_SCM_write_addr;
   logic [SCM_DATA_WIDTH-1:0]                          refill_DATA_SCM_write_wdata;
   logic [NB_WAYS-1:0]                                 refill_DATA_SCM_write_way;



   logic [NB_WAYS-1:0]                                 refill_way_int;
   logic [FETCH_ADDR_WIDTH-1:0]                        refill_address_int;


   logic                                               fetch_req_int;
   logic [FETCH_ADDR_WIDTH-1:0]                        fetch_addr_int;
   logic [NB_WAYS-1:0]                                 fetch_way_int;

   logic [NB_CORES-1:0]                                fetch_ID_OH_int; // ID is one hot --> NB_CORES bit
   logic [$clog2(NB_CORES)-1:0]                        fetch_ID_BIN_int; // ID is one hot --> NB_CORES bit
   logic                                               fetch_gnt_int;

   logic                                               fetch_rvalid_int;
   logic [FETCH_DATA_WIDTH-1:0]                        fetch_rdata_int;
   logic [NB_CORES:0]                                  fetch_rID_OH_int; // ID is one hot --> NB_CORES bit

   logic [NB_CORES-1:0][FETCH_ADDR_WIDTH+NB_WAYS-1:0]  compact_data_add_i;

   logic [$clog2(FETCH_DATA_WIDTH/AXI_DATA)-1:0]       rel_chunk_CS, rel_chunk_NS;
   logic [FETCH_DATA_WIDTH/AXI_DATA-1:0][AXI_DATA-1:0] axi_master_rdata_int;
   logic [AXI_ID-1:0]                                  axi_master_rid_int;
   logic                                               axi_master_rvalid_int;
   logic                                               sample_rdata;

   logic                                               fetch_rvalid_core, fetch_rvalid_pf;
   logic                                               fetch_req_muxed;
   logic [FETCH_ADDR_WIDTH-1:0]                        fetch_addr_muxed;
   logic [NB_WAYS-1:0]                                 fetch_way_muxed;
   logic                                               fetch_gnt_muxed;
   logic [NB_CORES:0]                                  fetch_ID_OH_muxed; // ID is one hot --> NB_CORES bit
   logic [$clog2(NB_CORES+1)-1:0]                      fetch_ID_BIN_muxed; // ID is one hot --> NB_CORES bit


   // Compact data sent along the address of the LOG interco: { FETCH_WAY, FETCH_ADDR }
   genvar i;
   generate
      for(i=0; i<NB_CORES; i++)
      begin
         assign compact_data_add_i[i] = {fetch_way_i[i], fetch_addr_i[i]}; 
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
   icache_intc 
   #(
      .ADDRESS_WIDTH  ( FETCH_ADDR_WIDTH+NB_WAYS         ),
      .N_CORES        ( NB_CORES                         ),
      .UID_WIDTH      ( NB_CORES                         ),
      .DATA_WIDTH     ( FETCH_DATA_WIDTH                 ),
      .N_CACHE_BANKS  ( 1                                ) // Single Main CC)
   )
   ICACHE_INTERCONNECT
   (
      .clk_i          ( clk                              ),
      .rst_ni         ( rst_n                            ),

      .request_i      ( fetch_req_i                      ), // Data request
      .address_i      ( compact_data_add_i               ), // Data request Address
      .grant_o        ( fetch_gnt_o                      ), // 
      .response_o     ( fetch_rvalid_o                   ), // Data Response Valid (For LOAD/STORE commands)
      .read_data_o    ( fetch_rdata_o                    ), // Data Response DATA (For LOAD commands)

      .request_o      ( fetch_req_int                    ), // Data request
      .address_o      ( {fetch_way_int,fetch_addr_int}   ), // Data request Address
      .UID_o          ( fetch_ID_OH_int                  ), // Data request Address
      .grant_i        ( fetch_gnt_int                    ), // Data Grant
      .read_data_i    ( fetch_rdata_int                  ), // valid REspone (must be accepted always)
      .response_i     ( fetch_rvalid_core                ), // Data Response ID (For LOAD commands)
      .response_UID_i ( fetch_rID_OH_int[NB_CORES-1:0]   )  // Data Response DATA (For LOAD and STORE)
   );


   ///////////////////////////////////////////////////////////////////////////////////////////
   // ██████╗ ███████╗   ███╗   ███╗██╗███████╗███████╗        ███╗   ███╗██╗   ██╗██╗  ██╗ //
   // ██╔══██╗██╔════╝   ████╗ ████║██║██╔════╝██╔════╝        ████╗ ████║██║   ██║╚██╗██╔╝ //
   // ██████╔╝█████╗     ██╔████╔██║██║███████╗███████╗        ██╔████╔██║██║   ██║ ╚███╔╝  //
   // ██╔═══╝ ██╔══╝     ██║╚██╔╝██║██║╚════██║╚════██║        ██║╚██╔╝██║██║   ██║ ██╔██╗  //
   // ██║     ██║███████╗██║ ╚═╝ ██║██║███████║███████║███████╗██║ ╚═╝ ██║╚██████╔╝██╔╝ ██╗ //
   // ╚═╝     ╚═╝╚══════╝╚═╝     ╚═╝╚═╝╚══════╝╚══════╝╚══════╝╚═╝     ╚═╝ ╚═════╝ ╚═╝  ╚═╝ //
   ///////////////////////////////////////////////////////////////////////////////////////////
   pf_miss_mux 
   #(
      .ADDR_WIDTH ( FETCH_ADDR_WIDTH+NB_WAYS ), 
      .ID_WIDTH   ( NB_CORES+1               )
   )
   i_pf_miss_mux
   (
      .arb_flag_i  ( 1'b0                                ),  // Max Priority on CH0 (Cores)
      
      // Main Inpu ports
      //# CH0
      .instr_req0_i ( fetch_req_int                      ),
      .instr_gnt0_o ( fetch_gnt_int                      ),
      .instr_add0_i ( {fetch_way_int,fetch_addr_int}     ),
      .instr_ID0_i  ( {1'b0,fetch_ID_OH_int}             ),
      //# CH1
      .instr_req1_i ( pf_fetch_req_i                     ),
      .instr_add1_i ( {pf_fetch_way_i,pf_fetch_addr_i}   ),
      .instr_ID1_i  ( {1'b1,{NB_CORES{1'b0}}}            ),     
      .instr_gnt1_o ( pf_fetch_gnt_o                     ),   

      // Mupliplexed request
      .instr_add_o  ( {fetch_way_muxed,fetch_addr_muxed} ),
      .instr_req_o  ( fetch_req_muxed                    ),
      .instr_ID_o   ( fetch_ID_OH_muxed                  ),          
      .instr_gnt_i  ( fetch_gnt_muxed                    )
    );


   assign fetch_rvalid_core = fetch_rvalid_int & (|fetch_rID_OH_int[NB_CORES-1:0]);
   assign fetch_rvalid_pf   = fetch_rvalid_int & fetch_rID_OH_int[NB_CORES]; // Not Used



   //////////////////////////////////////////////////////////////
   // ███╗   ███╗ █████╗ ██╗███╗   ██╗         ██████╗ ██████╗ //
   // ████╗ ████║██╔══██╗██║████╗  ██║        ██╔════╝██╔════╝ //
   // ██╔████╔██║███████║██║██╔██╗ ██║        ██║     ██║      //
   // ██║╚██╔╝██║██╔══██║██║██║╚██╗██║        ██║     ██║      //
   // ██║ ╚═╝ ██║██║  ██║██║██║ ╚████║███████╗╚██████╗╚██████╗ //
   // ╚═╝     ╚═╝╚═╝  ╚═╝╚═╝╚═╝  ╚═══╝╚══════╝ ╚═════╝ ╚═════╝ //
   //////////////////////////////////////////////////////////////
   central_controller_128
   #(
      .ID_WIDTH       ( NB_CORES+1        ),
      .ADDR_WIDTH     ( FETCH_ADDR_WIDTH  ),
      .DATA_WIDTH     ( FETCH_DATA_WIDTH  ),
      .DEPTH          ( 16                ),


      .SCM_ADDR_WIDTH ( SCM_ADDR_WIDTH    ),
      .SCM_TAG_WIDTH  ( SCM_TAG_WIDTH     ),
      .SCM_DATA_WIDTH ( SCM_DATA_WIDTH    ),
      .NB_BANKS       ( NB_BANKS          ),
      .NB_WAYS        ( NB_WAYS           ), 
      .NB_CORES       ( NB_CORES          ),

      .ADDR_CHECK_LSB ( 4                 ),
      .ADDR_CHECK_MSB ( 31                ),

      .ID_LSB         ( SET_ID_LSB        ),
      .ID_MSB         ( SET_ID_MSB        ),
      .TAG_LSB        ( TAG_LSB           ),
      .TAG_MSB        ( TAG_MSB           ),
      .DEST_LSB       ( 4                 ),
      .DEST_MSB       ( 4+$clog2(NB_BANKS))
   )
   CENTRAL_CONTROLLER
   (
      .clk                    ( clk                    ),
      .rst_n                  ( rst_n                  ),
      .test_en_i              ( test_en_i              ),

      .bypass_icache_i        ( bypass_icache_i        ),
      .cache_bypassed_o       ( cache_bypassed_o       ),
      .bypass_status_i        ( bypass_status_i        ),
      .empty_fifo_o           ( empty_fifo_o           ),
      .retry_fetch_o          ( retry_fetch_o          ),

      .flush_icache_i         ( flush_icache_i         ),
      .flush_ack_o            ( flush_ack_o            ),

      .sel_flush_req_i       ( sel_flush_req_i         ),
      .sel_flush_addr_i      ( sel_flush_addr_i        ),
      .sel_flush_ack_o       ( sel_flush_ack_o         ),

      .notify_refill_done_o   ( notify_refill_done_o   ),

      .fetch_req_i            ( fetch_req_muxed          ),
      .fetch_ID_BIN_i         ( fetch_ID_BIN_muxed       ),
      .fetch_ID_OH_i          ( fetch_ID_OH_muxed        ),
      .fetch_addr_i           ( fetch_addr_muxed         ),
      .fetch_way_i            ( fetch_way_muxed          ),
      .fetch_gnt_o            ( fetch_gnt_muxed          ),

      .fetch_rvalid_o         ( fetch_rvalid_int       ),
      .fetch_rdata_o          ( fetch_rdata_int        ),
      .fetch_rID_o            ( fetch_rID_OH_int       ),



      .AXI_req_o              ( axi_master_arvalid_o   ),
      .AXI_addr_o             ( axi_master_araddr_o[FETCH_ADDR_WIDTH-1:0] ),
      .AXI_ID_o               ( axi_master_arid_o      ),
      .AXI_gnt_i              ( axi_master_arready_i   ),

      .AXI_rvalid_i           ( axi_master_rvalid_int  ),
      .AXI_rID_i              ( axi_master_rid_int     ),
      .AXI_rdata_i            ( axi_master_rdata_int   ),

      // interface with WRITE PORT --> SCM Unified PORT
      .SCM_TAG_write_req_o    ( SCM_TAG_write_req_o    ),   
      .SCM_TAG_write_addr_o   ( SCM_TAG_write_addr_o   ),
      .SCM_TAG_write_dest_o   ( SCM_TAG_write_dest_o   ),
      .SCM_TAG_write_wdata_o  ( SCM_TAG_write_wdata_o  ),
      .SCM_TAG_write_way_o    ( SCM_TAG_write_way_o    ),  

      // interface with WRITE PORT --> SCM Unified PORT
      .SCM_DATA_write_req_o   ( SCM_DATA_write_req_o   ),   
      .SCM_DATA_write_addr_o  ( SCM_DATA_write_addr_o  ),    // DATA SCM has double number of rows
      .SCM_DATA_write_dest_o  ( SCM_DATA_write_dest_o  ),
      .SCM_DATA_write_wdata_o ( SCM_DATA_write_wdata_o ), 
      .SCM_DATA_write_way_o   ( SCM_DATA_write_way_o   )
   );
   if (AXI_ADDR > FETCH_ADDR_WIDTH) begin : gen_zero_extend_araddr
     assign axi_master_araddr_o[AXI_ADDR-1:FETCH_ADDR_WIDTH] = '0;
   end

   //always accept read data
   assign axi_master_rready_o   = 1'b1;
   assign axi_master_arlen_o    = 8'h01;   // FIXME for different cache line sizes
   assign axi_master_arsize_o   = 3'b011;  // FIXME for different cache line sizes
   assign axi_master_arburst_o  = 2'b01;    //for bursts>1, accept only incr burst=01
   assign axi_master_arlock_o   = 1'b0;     //only normal access supported axs_awlock=00
   assign axi_master_arcache_o  = 4'b0000;
   assign axi_master_arprot_o   = 3'b000;
   assign axi_master_arregion_o = '0;
   assign axi_master_aruser_o   = '0;
   assign axi_master_arqos_o    = 4'b0000;



   onehot_to_bin #( .ONEHOT_WIDTH(NB_CORES+1) ) ID_OH_to_BIN (.onehot(fetch_ID_OH_muxed), .bin(fetch_ID_BIN_muxed) );

   /////////////////////////////////////////////////////////////////////////////////////////////////////////
   //  █████╗ ██╗  ██╗██╗        ███████╗██╗███████╗███████╗         ██████╗ ██████╗ ███╗   ██╗██╗   ██╗ ///
   // ██╔══██╗╚██╗██╔╝██║        ██╔════╝██║╚══███╔╝██╔════╝        ██╔════╝██╔═══██╗████╗  ██║██║   ██║ ///
   // ███████║ ╚███╔╝ ██║        ███████╗██║  ███╔╝ █████╗          ██║     ██║   ██║██╔██╗ ██║██║   ██║ ///
   // ██╔══██║ ██╔██╗ ██║        ╚════██║██║ ███╔╝  ██╔══╝          ██║     ██║   ██║██║╚██╗██║╚██╗ ██╔╝ ///
   // ██║  ██║██╔╝ ██╗██║███████╗███████║██║███████╗███████╗███████╗╚██████╗╚██████╔╝██║ ╚████║ ╚████╔╝  ///
   // ╚═╝  ╚═╝╚═╝  ╚═╝╚═╝╚══════╝╚══════╝╚═╝╚══════╝╚══════╝╚══════╝ ╚═════╝ ╚═════╝ ╚═╝  ╚═══╝  ╚═══╝   ///
   /////////////////////////////////////////////////////////////////////////////////////////////////////////                                                                                                
   // AXI COMPACTOR 64 bit to 128 bit!!! Data comes back as 64 bit chunks.
   // This logic creates atomic responses (same with as the cache line size --> 128bit )
   always_ff @(posedge clk, negedge rst_n) 
   begin
      if(~rst_n) 
      begin
         CS_COMP <= IDLE_COMP;
         rel_chunk_CS <= '0;

         axi_master_rdata_int   <= '0;
         axi_master_rid_int     <= '0;
      end 
      else 
      begin
         CS_COMP <= NS_COMP;
         rel_chunk_CS <= rel_chunk_NS;

         if(sample_rdata)
         begin
            axi_master_rdata_int[rel_chunk_CS] <= axi_master_rdata_i;
            axi_master_rid_int                 <= axi_master_rid_i;
         end

      end
   end

   assign sample_rdata          = axi_master_rvalid_i;

   always_comb 
   begin
      rel_chunk_NS        = rel_chunk_CS;
      NS_COMP             = CS_COMP;

      case (CS_COMP)
         IDLE_COMP: 
         begin
            axi_master_rvalid_int = 1'b0;

            if(axi_master_rvalid_i)
            begin
               if(axi_master_rlast_i)
               begin
                  NS_COMP = DISP_COMP;
                  rel_chunk_NS = '0;
               end
               else
               begin
                  NS_COMP = IDLE_COMP;
                  rel_chunk_NS = rel_chunk_CS + 1'b1;
               end
            end
            else
            begin
               NS_COMP = IDLE_COMP;
               rel_chunk_NS = rel_chunk_CS;
            end

         end

         DISP_COMP: 
         begin
            axi_master_rvalid_int = 1'b1;
            NS_COMP = IDLE_COMP;

            if(axi_master_rvalid_i)
            begin
               if(axi_master_rlast_i)
               begin
                  NS_COMP = DISP_COMP;
                  rel_chunk_NS = '0;
               end
               else
               begin
                  NS_COMP = IDLE_COMP;
                  rel_chunk_NS = 1;  
               end
            end
            else
            begin
               NS_COMP = IDLE_COMP;
               rel_chunk_NS = '0;
            end
         end

         default: 
         begin
            NS_COMP = IDLE_COMP;
         end
      endcase
   
   end



endmodule
