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
// Module Name:    central_controller_128                                     //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    This block represents the master cache controller that     //
//                 receives the requests  (multiplexed) from different cache  //
//                 banks or HW prefetchre and checks if there are pending     //
//                 refill on that cache line, it also handles the writes on   //
//                 tag and data arrays.                                       //
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


module central_controller_128
#(
    parameter  ID_WIDTH       = 9, 
    parameter  LOG2_ID_WIDTH  = $clog2(ID_WIDTH),
    parameter  ADDR_WIDTH     = 32,
    parameter  DATA_WIDTH     = 128,
    parameter  DEPTH          = 16,
    parameter  LOG2_DEPTH     = $clog2(DEPTH),

    parameter  SCM_ADDR_WIDTH = 6,
    parameter  SCM_TAG_WIDTH  = 6,
    parameter  SCM_DATA_WIDTH = 128,
    parameter  NB_BANKS       = 4,
    parameter  NB_WAYS        = 4,
    parameter  NB_CORES       = 8,

    parameter ADDR_CHECK_LSB  = 4,
    parameter ADDR_CHECK_MSB  = ADDR_WIDTH-1,

    parameter ID_LSB          = 6,
    parameter ID_MSB          = 11,
    parameter TAG_LSB         = 12,
    parameter TAG_MSB         = SCM_TAG_WIDTH+TAG_LSB-2,
    parameter DEST_LSB        = 4,
    parameter DEST_MSB        = 5
)
(
    input  logic                                       clk,
    input  logic                                       rst_n,
    input  logic                                       test_en_i,

    input  logic                                       bypass_icache_i,
    output logic                                       cache_bypassed_o,
    input  logic [NB_CORES:0]                          bypass_status_i,

    input  logic                                       flush_icache_i,
    output logic                                       flush_ack_o,

   input  logic                                        sel_flush_req_i,
   input  logic [ADDR_WIDTH-1:0]                       sel_flush_addr_i,
   output logic                                        sel_flush_ack_o,

    output logic                                       empty_fifo_o,
    output logic [ID_WIDTH-1:0]                        retry_fetch_o,


    output logic [ID_WIDTH-1:0]                        notify_refill_done_o,
    

    input  logic                                       fetch_req_i,
    input  logic [LOG2_ID_WIDTH-1:0]                   fetch_ID_BIN_i,
    input  logic [ID_WIDTH-1:0]                        fetch_ID_OH_i,
    input  logic [ADDR_WIDTH-1:0]                      fetch_addr_i,
    input  logic [NB_WAYS-1:0]                         fetch_way_i,
    output logic                                       fetch_gnt_o,

    output logic                                       fetch_rvalid_o,
    output logic [DATA_WIDTH-1:0]                      fetch_rdata_o,
    output logic [ID_WIDTH-1:0]                        fetch_rID_o,



    output logic                                       AXI_req_o,
    output logic [ADDR_WIDTH-1:0]                      AXI_addr_o,
    output logic [LOG2_DEPTH-1:0]                      AXI_ID_o,
    input  logic                                       AXI_gnt_i,
    
    input  logic                                       AXI_rvalid_i,
    input  logic [LOG2_DEPTH-1:0]                      AXI_rID_i,
    input  logic [DATA_WIDTH-1:0]                      AXI_rdata_i,

   output logic                                        SCM_TAG_write_req_o,   
   output logic [SCM_ADDR_WIDTH-1:0]                   SCM_TAG_write_addr_o,
   output logic [$clog2(NB_BANKS)-1:0]                 SCM_TAG_write_dest_o,
   output logic [SCM_TAG_WIDTH-1:0]                    SCM_TAG_write_wdata_o,
   output logic [NB_WAYS-1:0]                          SCM_TAG_write_way_o,  

   // interface with WRITE PORT --> SCM Unified PORT
   output logic                                        SCM_DATA_write_req_o,   
   output logic [SCM_ADDR_WIDTH-1:0]                   SCM_DATA_write_addr_o,    // DATA SCM has double number of rows
   output logic [$clog2(NB_BANKS)-1:0]                 SCM_DATA_write_dest_o,
   output logic [SCM_DATA_WIDTH-1:0]                   SCM_DATA_write_wdata_o, 
   output logic [NB_WAYS-1:0]                          SCM_DATA_write_way_o  

);

   // STATE ENCODING
   enum logic [2:0] {INVALIDATE, BYPASSED, WAIT_EMPTY_BYPASS_FIFO, ENABLED, GOING_BYPASS, FLUSH_SET_ID } CS, NS;

   // signals declaration
   logic [$clog2(NB_BANKS)+SCM_ADDR_WIDTH-1:0]   counter_CS, counter_NS;

   logic                      CAM_empty;
   //TO REFILL CAM 
   logic                      CAM_grant;
   logic                      CAM_fetch_req;
   // From CAM to AXI MUX
   logic                      CAM_AXI_req;
   logic [ADDR_WIDTH-1:0]     CAM_AXI_addr;
   logic [LOG2_DEPTH-1:0]     CAM_AXI_ID;

   // for refill PURPOSE ONLY
   logic [ADDR_WIDTH-1:0]     CAM_refill_addr;
   logic [ID_WIDTH-1:0]       CAM_refill_ID;
   logic [NB_WAYS-1:0]        CAM_refill_way;

   logic                      fifo_rel_chunk_gnt;
   logic                      fifo_rel_chunk_valid;

   // Notify to different cache bank as soon the refill is committed in the DAT/TAG.
   // A new fetch attempt will be performed
   assign notify_refill_done_o = (~cache_bypassed_o & AXI_rvalid_i) ? CAM_refill_ID : '0;

   // CS and Counters Flip Flops
   always_ff @(posedge clk or negedge rst_n) 
   begin : Seq_CS_counters
      if(~rst_n) 
      begin
         CS         <= INVALIDATE;
         counter_CS <= '0;
      end 
      else 
      begin
         CS         <= NS;
         counter_CS <= counter_NS;
      end
   end


    always_comb 
    begin : Comb_logic_main_FSM

        // Default values for FSM outputs
        NS                     = CS;
        counter_NS             = counter_CS;

        fetch_gnt_o            = 1'b0;
        
        fetch_rvalid_o         = 1'b0;

        fetch_rdata_o          = AXI_rdata_i;
        fetch_rID_o            = 1<<AXI_rID_i;


        AXI_req_o              = 1'b0;
        AXI_addr_o             = '0;
        AXI_ID_o               = '0;

        flush_ack_o            = 1'b0;
        sel_flush_ack_o        = 1'b0;

        SCM_TAG_write_req_o    = 1'b0;
        SCM_TAG_write_addr_o   = '0;
        SCM_TAG_write_dest_o   = '0;
        SCM_TAG_write_wdata_o  = '0;
        SCM_TAG_write_way_o    = '0;

        SCM_DATA_write_req_o   = '0;
        SCM_DATA_write_way_o   = '0;
        SCM_DATA_write_addr_o  = '0;
        SCM_DATA_write_dest_o  = '0;
        SCM_DATA_write_wdata_o = '0;

        // by default cache is disabled
        cache_bypassed_o       = 1'b1;

        case(CS)

            // STATE used to FLUSH one particular SET ID
            FLUSH_SET_ID:
            begin
               // Flush the cache lines with that SET ID --> sel_flush_addr_i[ID_MSB:ID_LSB];
               SCM_TAG_write_req_o    = 1'b1;
               SCM_TAG_write_addr_o   = sel_flush_addr_i[ID_MSB:ID_LSB];
               SCM_TAG_write_dest_o   = sel_flush_addr_i[DEST_MSB:DEST_LSB];
               SCM_TAG_write_wdata_o  = '0;
               SCM_TAG_write_way_o    = '1;
               cache_bypassed_o       = 1'b0;

               sel_flush_ack_o        = 1'b1;

               // at any point in time check if there are Bypass request. 
               // In case, just serve it and go in the proper state
               if(bypass_icache_i)
                  NS = BYPASSED;
               else
                  NS = ENABLED;
            end


            // State used to invalidate the cache
            INVALIDATE:
            begin
                // Invalidate all cache Lines
                SCM_TAG_write_req_o    = 1'b1;
                SCM_TAG_write_addr_o   = counter_CS[SCM_ADDR_WIDTH-1:0];
                SCM_TAG_write_dest_o   = counter_CS[$clog2(NB_BANKS)+SCM_ADDR_WIDTH-1:SCM_ADDR_WIDTH];
                SCM_TAG_write_wdata_o  = '0;
                SCM_TAG_write_way_o    = '1;
                cache_bypassed_o       = 1'b1;

                // Iterate on all cache lines (not in parallel, one cache line at the time)
                if(counter_CS < NB_BANKS * (2**SCM_ADDR_WIDTH) -1 )
                begin
                   NS = INVALIDATE;
                   counter_NS = counter_CS + 1'b1;
                end
                else
                begin
                    flush_ack_o = 1'b1;
                    
                    if(bypass_icache_i)
                        NS = BYPASSED;
                    else
                        NS = ENABLED;

                   counter_NS = '0;
                end
            end

            //Main state for cache bypassed (not enabled). 
            BYPASSED:
            begin
                   cache_bypassed_o = 1'b1;
                   flush_ack_o      = 1'b1;
                   sel_flush_ack_o  = 1'b1;
                   
                   fetch_rvalid_o  = AXI_rvalid_i;
                   fetch_gnt_o     = AXI_gnt_i & fifo_rel_chunk_gnt;
                   
                   AXI_req_o       = fetch_req_i & fifo_rel_chunk_gnt;
                   AXI_addr_o      = fetch_addr_i & 32'hFFFF_FFF0; // Mast bits from [3:0] --> 128 bit access
                   
                   // DEPTH > ID_WIDTH
                   if(LOG2_DEPTH == LOG2_ID_WIDTH)
                      AXI_ID_o        = fetch_ID_BIN_i;
                   else 
                      AXI_ID_o        = {  {(LOG2_DEPTH-LOG2_ID_WIDTH){1'b0}} , fetch_ID_BIN_i};



                   // Check if there is a bypass req,  a flush or a selective FLush
                   // If one of these signals is 1, then thre is nothing to do
                   // cache is already bypassed, so flush or selective flush does
                   // not perform any further action.
                   if(bypass_icache_i)
                       NS = BYPASSED;
                   else
                       NS = WAIT_EMPTY_BYPASS_FIFO;
            end


            // Stay in this state untill the 
            WAIT_EMPTY_BYPASS_FIFO:
            begin
                cache_bypassed_o  = 1'b1;

                fetch_rvalid_o  = AXI_rvalid_i;


                fetch_gnt_o = 1'b0;
                if(fifo_rel_chunk_valid == 1'b0)  // no longer transactions in the BYPASS FIFO.
                begin
                     NS = INVALIDATE;
                end
                else
                begin
                   NS = WAIT_EMPTY_BYPASS_FIFO;
                end
            end


            // Main State When cache is Enabled
            ENABLED: 
            begin
               cache_bypassed_o  = 1'b0;

               AXI_req_o       = CAM_AXI_req;
               AXI_addr_o      = CAM_AXI_addr;
               AXI_ID_o        = CAM_AXI_ID;

               fetch_gnt_o     = CAM_grant;
               fetch_rvalid_o  = 1'b0;


               // Check if there is a bypass req,  a flush or a selective FLush
               // If one of these signals is 1, then the controller performs the
               // right action
               if( bypass_icache_i | flush_icache_i | sel_flush_req_i )
               begin
                  NS = GOING_BYPASS;
               end
               else
               begin
                  NS = ENABLED ;
               end



               // Handle teh Backwrite of the refill in the SCM banks
               SCM_DATA_write_way_o           = CAM_refill_way;
               SCM_DATA_write_addr_o          = CAM_refill_addr[ID_MSB:ID_LSB];
               SCM_DATA_write_dest_o          = CAM_refill_addr[DEST_MSB:DEST_LSB] ;
               SCM_DATA_write_wdata_o         = AXI_rdata_i;

               SCM_TAG_write_way_o            = CAM_refill_way;
               SCM_TAG_write_addr_o           = CAM_refill_addr[ID_MSB:ID_LSB];
               SCM_TAG_write_dest_o           = CAM_refill_addr[DEST_MSB:DEST_LSB];

               if(AXI_rvalid_i)
               begin
                  SCM_DATA_write_req_o   = ~cache_bypassed_o;
                  SCM_TAG_write_req_o    = ~cache_bypassed_o;
                  SCM_TAG_write_wdata_o  = {1'b1, CAM_refill_addr[TAG_MSB:TAG_LSB]};
               end
               else // AXI_rvalid_i == 0
               begin
                  SCM_DATA_write_req_o   = '0;
                  SCM_TAG_write_req_o    = '0;
                  SCM_TAG_write_wdata_o  = '0;
               end

            end

            // Cache is Enabled but there was a Request to Disable,
            // Empty the refill storage before switching
            GOING_BYPASS:
            begin
               fetch_gnt_o                    = 1'b0;
               cache_bypassed_o               = 1'b0;

               // Handle teh Backwrite of the refill in the SCM banks
               SCM_DATA_write_way_o           = CAM_refill_way;
               SCM_DATA_write_addr_o          = CAM_refill_addr[ID_MSB:ID_LSB];
               SCM_DATA_write_dest_o          = CAM_refill_addr[DEST_MSB:DEST_LSB] ;
               SCM_DATA_write_wdata_o         = AXI_rdata_i;

               SCM_TAG_write_way_o            = CAM_refill_way;
               SCM_TAG_write_addr_o           = CAM_refill_addr[ID_MSB:ID_LSB];
               SCM_TAG_write_dest_o           = CAM_refill_addr[DEST_MSB:DEST_LSB];

                if(AXI_rvalid_i)
                begin
                       SCM_DATA_write_req_o      = ~cache_bypassed_o;
                       SCM_TAG_write_req_o       = ~cache_bypassed_o;
                       SCM_TAG_write_wdata_o     = {1'b1, CAM_refill_addr[TAG_MSB:TAG_LSB]};
                end
                else // AXI_rvalid_i == 0
                begin
                       SCM_DATA_write_req_o      = '0;
                       SCM_TAG_write_req_o       = '0;
                       SCM_TAG_write_wdata_o     = '0;
                end


                //Finally , if the CAM is EMpty, switch to BYPASSED state
                if(CAM_empty)
                begin
                     if( flush_icache_i ) 
                     begin
                        NS = INVALIDATE;
                     end
                     else  if( sel_flush_req_i )
                           begin
                              NS = FLUSH_SET_ID;
                           end
                           else
                           begin
                              NS = BYPASSED;
                           end
                end
                else // CAM is not empty
                begin
                    NS = GOING_BYPASS;
                end
            end


            default: 
            begin
              // In case something goes wrong, commute to Invalidated then --> Bypass or Enabled
              cache_bypassed_o  = 1'b1;
              NS                = INVALIDATE;
            end

        endcase
    end


    // This FIFO holds information about in fligth fetches when cache is bypassed
    generic_fifo 
    #( 
       .DATA_WIDTH ( 1      ),
       .DATA_DEPTH ( DEPTH  )
    )
    REL_CHUNK_FIFO
    (
       .clk         ( clk                                        ),
       .rst_n       ( rst_n                                      ),

       .data_i      (                                            ),
       .valid_i     ( fetch_req_i & AXI_gnt_i & (CS == BYPASSED) ), // cache in bypass mode, LOOKUPTABLE empty
       .grant_o     ( fifo_rel_chunk_gnt                         ),
       
       .data_o      (                                            ),
       .valid_o     ( fifo_rel_chunk_valid                       ),
       .grant_i     ( AXI_rvalid_i                               ),

       .test_mode_i ( test_en_i                                  )
    );



     // This storage is a CAM, that stores pending refills:
     // REfills are merged toghether if they compete to the same cache line.
     // in case multiple cache banks have requested to the same cache line (in different moments)
     // this cam updates these infos, and as soon the refill from axi side arrives, the master cache 
     // controller updates DATA/TAG and then notifies to those cache master to retry a fetch.
     merge_refill_cam_128_16
     #(
        .NB_WAYS         ( NB_WAYS         ),
        .ID_WIDTH        ( ID_WIDTH        ), 
        .LOG2_ID_WIDTH   ( LOG2_ID_WIDTH   ),
        .ADDR_WIDTH      ( ADDR_WIDTH      ),
        .DEPTH           ( 16              ),
        .LOG2_DEPTH      ( 4               ),
        .ADDR_CHECK_LSB  ( ADDR_CHECK_LSB  ),
        .ADDR_CHECK_MSB  ( ADDR_CHECK_MSB  )
     )
     MERGE_CAM
     (
        .clk            ( clk             ),
        .rst_n          ( rst_n           ),

        .empty_o        ( CAM_empty       ),
        .retry_fetch_o  ( retry_fetch_o   ),

        .fetch_req_i    ( fetch_req_i & fetch_gnt_o & ~cache_bypassed_o ),
        .fetch_ID_BIN_i ( fetch_ID_BIN_i  ),
        .fetch_ID_OH_i  ( fetch_ID_OH_i   ),
        .fetch_addr_i   ( fetch_addr_i    ),
        .fetch_way_i    ( fetch_way_i     ),
        .fetch_gnt_o    ( CAM_grant       ),

        .AXI_rvalid_i   ( AXI_rvalid_i    ),
        .AXI_rID_i      ( AXI_rID_i       ),

        .AXI_req_o      ( CAM_AXI_req     ),
        .AXI_addr_o     ( CAM_AXI_addr    ),
        .AXI_ID_o       ( CAM_AXI_ID      ),
        .AXI_gnt_i      ( AXI_gnt_i       ),


        .refill_addr_o  ( CAM_refill_addr ),
        .refill_ID_o    ( CAM_refill_ID   ),
        .refill_way_o   ( CAM_refill_way  )
     );


   assign empty_fifo_o = CAM_empty & ~fifo_rel_chunk_valid;


endmodule // central_controller
