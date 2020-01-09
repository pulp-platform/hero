// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


`define OKAY    2'b00
`define EXOKAY  2'b01
`define SLVERR  2'b10
`define DECERR  2'b11

module AXI4_REFILL_Resp_Deserializer
#(
   parameter CACHE_LINE         = 4,
   parameter ICACHE_DATA_WIDTH  = 32,
   parameter FIFO_DEPTH         = 8,
   parameter AXI_ID             = 6,
   parameter AXI_DATA           = 64,
   parameter AXI_USER           = 8
)
(
   input  logic                                                rst_n,
   input  logic                                                clk,
   input  logic                                                test_en_i,

   input  logic                                                bypass_icache_i,

   input  logic [AXI_ID-1:0]                                   init_rid_i,
   input  logic [AXI_DATA-1:0]                                 init_rdata_i,
   input  logic [ 1:0]                                         init_rresp_i,
   input  logic                                                init_rlast_i,
   input  logic [ AXI_USER-1:0]                                init_ruser_i,
   input  logic                                                init_rvalid_i,
   output logic                                                init_rready_o,

   output  logic [AXI_ID-1:0]                                  init_rid_o,
   output  logic [CACHE_LINE-1:0][ICACHE_DATA_WIDTH-1:0]       init_rdata_o,
   output  logic [ 1:0]                                        init_rresp_o,
   output  logic [ AXI_USER-1:0]                               init_ruser_o,
   output  logic                                               init_rvalid_o,
   input   logic                                               init_rready_i
);

   localparam FIFO_DATA_WIDTH      = 1 + AXI_ID + 2 + AXI_USER + AXI_DATA ;
   localparam WIDE_FIFO_DATA_WIDTH =     AXI_ID + 2 + AXI_USER + ICACHE_DATA_WIDTH * CACHE_LINE ;


   // FIFO 64 bit to COMPACTOR (WIDE FIFO)
   logic [AXI_ID-1:0]                                                  init_rid_int;
   logic [AXI_DATA-1:0]                                                init_rdata_int;
   logic [ 1:0]                                                        init_rresp_int;
   logic                                                               init_rlast_int;
   logic [ AXI_USER-1:0]                                               init_ruser_int;
   logic                                                               init_rvalid_int;
   logic                                                               init_rready_int;

   logic [AXI_ID-1:0]                                                  init_rid_latched;
   logic [ (ICACHE_DATA_WIDTH*CACHE_LINE)/AXI_DATA-1:0][AXI_DATA-1:0]  init_rdata_latched;
   logic [ 1:0]                                                        init_rresp_latched;
   logic                                                               init_rlast_latched;
   logic [ AXI_USER-1:0]                                               init_ruser_latched;
   logic                                                               init_rvalid_latched;
   logic                                                               init_rready_latched;

   enum logic [1:0] { IDLE, DISP_SINGLE_DATA, COLLECT_BURST}           CS, NS;


   logic                                                               latch_data;
   logic                                                               latch_ctrl;


   logic                                                               r_valid_wfifo;
   logic                                                               r_ready_wfifo;

   logic                                                               r_ready_int;
   logic                                                               r_valid_int;

   logic [$clog2(CACHE_LINE*ICACHE_DATA_WIDTH/AXI_DATA)-1:0]           BurstCounterCS, BurstCounterNS;

   // CODE STARTs HERE!!!!!!!!!!!!!!!!!!!!!!!!






   // Narrow FIFO concatenated Signals
   logic [FIFO_DATA_WIDTH-1:0]                         D_IN;
   logic [FIFO_DATA_WIDTH-1:0]                         D_INT;

   // Wide FIFO concatenated Signals
   logic [WIDE_FIFO_DATA_WIDTH-1:0]                    DIN;
   logic [WIDE_FIFO_DATA_WIDTH-1:0]                    DOUT;


   assign        {init_ruser_int, init_rid_int, init_rlast_int, init_rresp_int, init_rdata_int } = D_INT;
   assign D_IN = {init_ruser_i,   init_rid_i,   init_rlast_i,   init_rresp_i,   init_rdata_i   };

   // Input and output array used on the WIDE INPUT FIFO: takes data from The latched array and it moves on the  
   assign    DIN = {init_ruser_latched, init_rid_latched, init_rresp_latched, init_rdata_latched};
   assign          {init_ruser_o,       init_rid_o,       init_rresp_o,       init_rdata_o      } = DOUT;




   // DESERIALIZER SEQUENTIAL BLOCK
   always_ff @(posedge clk, negedge rst_n)
   begin : UPDATE_CS
     if(rst_n == 1'b0)
       begin
         CS <= IDLE;
         BurstCounterCS          <= '0;
         init_ruser_latched      <= '0;
         init_rid_latched        <= 1'b0;
         init_rresp_latched      <= `OKAY;
         init_rdata_latched      <= '0;
       end
     else //  ~ rst_n == 1'b0
       begin
         CS <= NS;
         BurstCounterCS <= BurstCounterNS;

         if(latch_ctrl)
         begin
           init_rresp_latched <= init_rresp_int;
           init_ruser_latched <= init_ruser_int;
           init_rid_latched   <= init_rid_int;
         end


         if(latch_data)
         begin
           init_rdata_latched[BurstCounterCS] <= init_rdata_int;
         end

       end // ~ rst_n == 1'b1
   end



   // DESERIALIZER COMB BLOCK: FSM    
   always_comb
   begin : UPDATE_NS_AND_OUT

     r_valid_wfifo             = 1'b0;
     r_ready_int               = 1'b0;
     latch_ctrl                = 1'b0;
     latch_data                = 1'b0;
     BurstCounterNS            = BurstCounterCS;

     case(CS)

     IDLE: 
     begin
         r_ready_int           = 1'b1;
         r_valid_wfifo         = 1'b0;

         if(r_valid_int)
           begin
             latch_ctrl        = 1'b1;
             latch_data        = 1'b1;

             if(init_rlast_int)
             begin
                 BurstCounterNS      = '0;
                 NS                  = DISP_SINGLE_DATA;
             end
             else
             begin
                 BurstCounterNS      = BurstCounterCS+1'b1;
                 NS                  = COLLECT_BURST;
             end


           end
         else
           begin
                 latch_ctrl          = 1'b0;
                 latch_data          = 1'b0;
                 NS                  = IDLE;
                 BurstCounterNS      = '0;
           end
     end //~IDLE


     DISP_SINGLE_DATA: 
     begin
           r_ready_int     = r_ready_wfifo;
           r_valid_wfifo   = 1'b1;

           if(r_ready_wfifo)
           begin

               if(r_valid_int)
               begin
                       latch_ctrl             = 1'b1;
                       latch_data             = 1'b1;

                       if(init_rlast_int)
                       begin
                           BurstCounterNS     = '0;
                           NS                 = DISP_SINGLE_DATA;
                       end
                       else
                       begin
                           BurstCounterNS     = BurstCounterCS+1'b1;
                           NS                 = COLLECT_BURST;
                       end


               end
               else
               begin
                           latch_ctrl         = 1'b0;
                           latch_data         = 1'b0;
                           NS                 = IDLE;
                           BurstCounterNS     = '0;
               end
           end
           else //~if(r_ready_wfifo)
           begin
               NS = DISP_SINGLE_DATA;
               BurstCounterNS            = BurstCounterCS;
               latch_ctrl                = 1'b0;
               latch_data                = 1'b0;
           end
     end //~ DISP_SINGLE_DATA


      COLLECT_BURST:
      begin    
         r_ready_int                 = 1'b1;
         if(r_valid_int)
         begin
            if( init_rlast_int) 
            begin
                  NS              = DISP_SINGLE_DATA;
                  BurstCounterNS  = '0;
                  latch_ctrl      = 1'b0;
                  latch_data      = 1'b1;
            end
            else
            begin
                  NS              = COLLECT_BURST;
                  BurstCounterNS  = BurstCounterCS+1'b1;
                  latch_ctrl      = 1'b0;
                  latch_data      = 1'b1;
            end
         end
         else
         begin
         NS                    = COLLECT_BURST;
         BurstCounterNS        = BurstCounterCS;
         latch_ctrl            = 1'b0;
         latch_data            = 1'b0;                    
         end                    
      end //~COLLECT_BURST

     default: 
     begin
         NS                        = IDLE;
     end //~default
     endcase

   end  


   // OUTPUT FIFO (CACHE_LINE*64 bit on the Cache Controller Side): Atomic Transactions   
   REP_buffer_4 
   #(
      .DATAWIDTH ( WIDE_FIFO_DATA_WIDTH)
   )
   REPEATER
   (
      .clk       ( clk            ), 
      .rst_n     ( rst_n          ),   
      //PUSH
      .DATA_in   ( DIN            ), 
      .VALID_in  ( r_valid_wfifo  ), 
      .GRANT_out ( r_ready_wfifo  ),    
      // POP
      .DATA_out  ( DOUT           ), 
      .VALID_out ( init_rvalid_o  ), 
      .GRANT_in  ( init_rready_i  )
   );

generate

    case(ICACHE_DATA_WIDTH)
    128,256,512: 
    begin
        // Input FIFO (64 bit on the AXI REFILL RESP Side)
        generic_fifo 
        #( 
                .DATA_WIDTH(FIFO_DATA_WIDTH),
                .DATA_DEPTH(FIFO_DEPTH)
        )
        REQUEST_FIFO
        (
                .clk          ( clk            ),
                .rst_n        ( rst_n          ),
                .test_mode_i  ( test_en_i      ),
                .data_i       ( D_IN           ),
                .valid_i      ( init_rvalid_i  ),
                .grant_o      ( init_rready_o  ),
                .data_o       ( D_INT          ),
                .valid_o      ( r_valid_int    ),
                .grant_i      ( r_ready_int    )
        );
    end
    
    default: 
    begin
        // Input FIFO (64 bit on the AXI REFILL RESP Side)
        generic_fifo
        #( 
                .DATA_WIDTH(FIFO_DATA_WIDTH),
                .DATA_DEPTH(FIFO_DEPTH)
        )
        REQUEST_FIFO                  
        (
                .clk          ( clk                              ),
                .rst_n        ( rst_n                            ),
                .test_mode_i  ( test_en_i                        ),
                .data_i       ( D_IN                             ),
                .valid_i      ( init_rvalid_i & ~bypass_icache_i ),
                .grant_o      ( init_rready_o                    ),
                .data_o       ( D_INT                            ),
                .valid_o      ( r_valid_int                      ),
                .grant_i      ( r_ready_int                      )
        );
    end
    endcase

endgenerate

endmodule
