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
// Module Name:    icache_bank_mp_128_PF                                      //
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

`define USE_REQ_BUFFER

module icache_bank_mp_128_PF
#(
   parameter FETCH_ADDR_WIDTH = 32,
   parameter FETCH_DATA_WIDTH = 128,

   parameter NB_CORES        = 4,
   parameter BANK_ID         = 0,
   parameter NB_BANKS        = 4,
   parameter NB_WAYS         = 4,
   parameter CACHE_LINE      = 1,

   parameter SCM_ADDR_WIDTH  = 16,
   parameter SCM_TAG_WIDTH   = 6,
   parameter SCM_DATA_WIDTH  = 128,

   parameter SET_ID_LSB      = $clog2(NB_BANKS)+$clog2(SCM_DATA_WIDTH*CACHE_LINE)-3,
   parameter SET_ID_MSB      = SET_ID_LSB + SCM_ADDR_WIDTH - 1,
   parameter TAG_LSB         = SET_ID_MSB + 1,
   parameter TAG_MSB         = TAG_LSB + SCM_TAG_WIDTH - 2,

   parameter AXI_ID          = 4,
   parameter AXI_ADDR        = FETCH_ADDR_WIDTH,
   parameter AXI_USER        = 6,
   parameter AXI_DATA        = 64
)
(
   input logic                                                  clk,
   input logic                                                  rst_n,
   input logic                                                  test_en_i,

   input  logic                                                 notify_refill_done_i,
   input  logic                                                 bypass_icache_i,
   input  logic                                                 empty_fifo_i,
   output logic                                                 cache_is_bypassed_o,
   input  logic [NB_CORES:0]                                    bypass_status_i,
   input  logic                                                 retry_fetch_i,

   // interface with processor
   input  logic                                                 fetch_req_i,
   input  logic [FETCH_ADDR_WIDTH-1:0]                          fetch_addr_i,
   output logic                                                 fetch_gnt_o,
   output logic                                                 fetch_rvalid_o,

   // interface with READ PORT --> SCM TAG
   output logic [NB_BANKS-1:0]                                  TAG_read_req_o,   
   output logic [SCM_ADDR_WIDTH-1:0]                            TAG_read_addr_o,
   input  logic [NB_BANKS-1:0][NB_WAYS-1:0][SCM_TAG_WIDTH-1:0]  TAG_read_rdata_i,


   // Interface to cache_controller_to_axi
   output logic                                                 fetch_req_o,
   output logic [FETCH_ADDR_WIDTH-1:0]                          fetch_addr_o,
   output logic [NB_WAYS-1:0]                                   fetch_way_o,  
   input  logic                                                 fetch_gnt_i,
   input  logic                                                 fetch_rvalid_i
);


   localparam OFFSET     = $clog2(SCM_DATA_WIDTH*CACHE_LINE)-3;

   // Finite State declaration: PS is Past State, used only for Statistic (perf Counters)
   enum logic [2:0] { DISABLED_ICACHE, WAIT_NOTIFICATION, OPERATIVE, REQ_REFILL , WAIT_EMPTY_FIFOS, ENTER_BYPASS } CS, NS, PS;

   // signals declaration
   logic [FETCH_ADDR_WIDTH-1:0]                    fetch_addr_Q;
   logic                                           fetch_req_Q;

   logic                                           save_fetch;
   logic                                           save_pipe_status;
   logic                                           clear_pipe;
   logic                                           enable_pipe;

   logic [$clog2(NB_BANKS)-1:0]                    fetch_dest_Q;         //Target BANK
   logic [NB_WAYS-1:0][SCM_TAG_WIDTH-1:0]          TAG_read_rdata_int;

   logic [NB_WAYS-1:0]                             way_match;
   logic [NB_WAYS-1:0]                             way_valid;
   logic [NB_WAYS-1:0]                             way_match_bin;
   logic [NB_WAYS-1:0]                             way_match_Q;
   logic [NB_WAYS-1:0]                             way_valid_Q;

   logic [NB_WAYS-1:0]                             random_way;  // In case of Way replacement // Driven By LFSR
   logic [$clog2(NB_WAYS)-1:0]                     first_available_way;
   logic [NB_WAYS-1:0]                             first_available_way_OH;

   logic [$clog2(NB_WAYS)-1:0]                     HIT_WAY;

   assign first_available_way_OH = 1 << first_available_way;



   int unsigned i,j,index;


   logic      update_lfsr;


   logic                                             fetch_req_int;
   logic [FETCH_ADDR_WIDTH-1:0]                      fetch_addr_int;
   logic [NB_WAYS-1:0]                               fetch_way_int;
   logic                                             fetch_gnt_int;
`ifdef USE_REQ_BUFFER
   logic [FETCH_ADDR_WIDTH+NB_WAYS-1:0]              s_data_in;
   logic [FETCH_ADDR_WIDTH+NB_WAYS-1:0]              s_data_out;
`endif



   // Sequential Logic (state, counters and registrered signals)
   always_ff @(posedge clk, negedge rst_n) 
   begin : Seq_logic
      if(~rst_n) 
      begin
          CS                  <= DISABLED_ICACHE;
          PS                  <= DISABLED_ICACHE;
          fetch_addr_Q        <= '0;
          fetch_req_Q         <= 1'b0;
          way_match_Q         <= '0;
          way_valid_Q         <= '0;
      end 
      else 
      begin
          CS <= NS;
          PS <= CS;

          if(save_pipe_status)
          begin
            way_match_Q <= way_match;
            way_valid_Q <= way_valid;
          end


          if(enable_pipe)
          begin
               fetch_req_Q    <= 1'b1;
               fetch_addr_Q   <= fetch_addr_i;
          end
          else  if(clear_pipe)
                begin
                     fetch_req_Q <= '0;
                end

      end
   end



   assign fetch_dest_Q        = fetch_addr_Q[$clog2(NB_BANKS)+OFFSET-1:OFFSET];
   assign TAG_read_rdata_int  = TAG_read_rdata_i[fetch_dest_Q]  ;

      

   // Logic to check TAG HIT/MISS
   // --------------------- //
   // TAG CHECK MULTI WAY   //
   // --------------------- //
   genvar k;
   generate
      for(k=0; k<NB_WAYS; k++)
      begin
         assign way_match[k]  = ((TAG_read_rdata_int[k][SCM_TAG_WIDTH-1] == 1'b1) && (TAG_read_rdata_int[k][SCM_TAG_WIDTH-2:0] == fetch_addr_Q[TAG_MSB:TAG_LSB]));
         assign way_valid[k]  = (TAG_read_rdata_int[k][SCM_TAG_WIDTH-1] == 1'b1);
      end
   endgenerate




  // Use this Buffer to split critical path from Private cache controller and the main cache controller
  // remember that there is a Interconenct between private CC and Main CC, used to multiplex the requests
`ifdef USE_REQ_BUFFER
   ////////////////////////////////////////////////////////////////////////////////////
   // ██████╗ ███████╗ ██████╗     ██████╗ ██╗   ██╗███████╗███████╗███████╗██████╗  //
   // ██╔══██╗██╔════╝██╔═══██╗    ██╔══██╗██║   ██║██╔════╝██╔════╝██╔════╝██╔══██╗ //
   // ██████╔╝█████╗  ██║   ██║    ██████╔╝██║   ██║█████╗  █████╗  █████╗  ██████╔╝ //
   // ██╔══██╗██╔══╝  ██║▄▄ ██║    ██╔══██╗██║   ██║██╔══╝  ██╔══╝  ██╔══╝  ██╔══██╗ //
   // ██║  ██║███████╗╚██████╔╝    ██████╔╝╚██████╔╝██║     ██║     ███████╗██║  ██║ //
   // ╚═╝  ╚═╝╚══════╝ ╚══▀▀═╝     ╚═════╝  ╚═════╝ ╚═╝     ╚═╝     ╚══════╝╚═╝  ╚═╝ //
   ////////////////////////////////////////////////////////////////////////////////////

   assign s_data_in = {fetch_way_int,  fetch_addr_int };
   assign             {fetch_way_o,    fetch_addr_o   } = s_data_out;
   generic_fifo
   #(
      .DATA_WIDTH ( FETCH_ADDR_WIDTH+NB_WAYS   ),
      .DATA_DEPTH ( 16                         ) // MAX 16 pending Fetches
   )
   miss_buffer
   (
      .clk           ( clk             ),
      .rst_n         ( rst_n           ),

      .data_i        ( s_data_in       ),
      .valid_i       ( fetch_req_int   ),
      .grant_o       ( fetch_gnt_int   ),

      .data_o        ( s_data_out      ),
      .valid_o       ( fetch_req_o     ),
      .grant_i       ( fetch_gnt_i     ),

      .test_mode_i   ( test_en_i       )
   );
`else
   assign fetch_way_o       = fetch_way_int;
   assign fetch_addr_o      = fetch_addr_int;
   assign fetch_req_o       = fetch_req_int;
   assign fetch_gnt_int     = fetch_gnt_i;
`endif



always_comb
begin : Comb_logic_FSM

   // default values for thre outputs FSM control signals
   TAG_read_req_o          = '0;
   TAG_read_addr_o         = fetch_addr_i[SET_ID_MSB:SET_ID_LSB];

   fetch_gnt_o             = 1'b0;
   fetch_rvalid_o          = 1'b0;

   fetch_req_int             = 1'b0;
   fetch_addr_int            = fetch_addr_i;
   fetch_way_int             = '0;


   save_fetch              = 1'b0;
   save_pipe_status        = 1'b0;
   enable_pipe             = 1'b0;
   clear_pipe              = 1'b0;
   cache_is_bypassed_o     = 1'b0;
   NS                      = CS;
   update_lfsr             = 1'b0;


   case(CS)

      // Primary state when cache is POwered UP:
      // Cache is bypassed so every fetch will be forwared directly to the main CC
      DISABLED_ICACHE: 
      begin
         clear_pipe          = 1'b1;
         cache_is_bypassed_o = 1'b1;

         // If cache is disabled, then 
         // Do not perform prefetching
         fetch_req_int       = 1'b0;
         fetch_gnt_o         = 1'b1;
         fetch_rvalid_o      = 1'b0; // Not used

         if(bypass_icache_i == 1'b1) // Already Bypassed
         begin
            NS = DISABLED_ICACHE;
         end
         else
         begin // Enable ICache
            NS = WAIT_EMPTY_FIFOS;
         end
      end


      // Cache is bypassed bu there is a pending fetch to be completed.
      // wait here until the fetch is concluded, then go in OPERATIVVE state.
      WAIT_EMPTY_FIFOS:
      begin
         clear_pipe            = 1'b1;
         cache_is_bypassed_o   = 1'b1;
         
         fetch_rvalid_o        = 1'b0;

         if(empty_fifo_i)
         begin
               NS = OPERATIVE; // Flushing is made in the central controller
         end
         else
         begin
               NS = WAIT_EMPTY_FIFOS;
         end
      end




      // Main state where the cache is enabled
      OPERATIVE: 
      begin
         cache_is_bypassed_o  = 1'b0;
         
         if(bypass_icache_i) // first check if the previous fetch has a miss or HIT
         begin
            
            fetch_gnt_o          = 1'b0;

            if(fetch_req_Q)
            begin
                if(|way_match)
                begin : HIT_BYP
                   NS = ENTER_BYPASS;

                   if(fetch_req_i == 1'b0)
                      clear_pipe = 1'b1;

                   fetch_rvalid_o  = 1'b1;

                end
                else 
                begin : MISS_BYP
                   // asks for the last refill, then goes into DISABLED state
                   NS               = REQ_REFILL;
                   save_fetch       = fetch_req_i;
                   save_pipe_status = 1'b1;
                end
            end //~if(fetch_req_Q == 1'b1)
            else
            begin
                NS = DISABLED_ICACHE;
                clear_pipe = 1'b1;
            end//~else(fetch_req_Q)
         end
         else
         begin
              
            
            //Read the DATA nd TAG
            TAG_read_req_o[fetch_addr_i[$clog2(NB_BANKS)-1+4:4]]  = fetch_req_i;
            TAG_read_addr_o = fetch_addr_i[SET_ID_MSB:SET_ID_LSB];

            if(fetch_req_Q)
            begin
                if(|way_match)
                begin : HIT
                   NS = OPERATIVE;
                   enable_pipe          = fetch_req_i;

                   if(fetch_req_i == 1'b0)
                      clear_pipe = 1'b1;

                   fetch_rvalid_o  = 1'b1;
                   fetch_gnt_o     = 1'b1;
                end
                else 
                begin : MISS

                   
                   fetch_req_int      = 1'b1;
                   fetch_addr_int     = fetch_addr_Q;

                   if(&way_valid) // all the lines are valid, invalidate one random line
                   begin
                         fetch_way_int = random_way;
                         update_lfsr = 1'b1;
                   end
                   else
                   begin
                         fetch_way_int = first_available_way_OH;
                         update_lfsr = 1'b0;
                   end

                   fetch_gnt_o     = fetch_gnt_int;
                   enable_pipe     = fetch_gnt_int;

                   if(fetch_gnt_int)
                   begin
                     NS              = OPERATIVE;
                     fetch_rvalid_o  = 1'b1;
                   end
                   else
                     NS = REQ_REFILL;

                   save_fetch       = fetch_req_i;
                   save_pipe_status = 1'b1;

                end
            end
            else
            begin
                NS = OPERATIVE;
                fetch_gnt_o     = 1'b1;
                enable_pipe     = fetch_req_i;
            end

         end

      end

      // state used to commute from CACHE beign enabled to serve a BYPASS request. 
      // it will stay here untill the pending refill/reques is served
      ENTER_BYPASS:
      begin
        fetch_gnt_o = 1'b0;
        fetch_rvalid_o = 1'b0;
        cache_is_bypassed_o = 1'b1;

        if(&bypass_status_i)
        begin
            NS = DISABLED_ICACHE;
        end
        else
        begin
            NS = ENTER_BYPASS;
        end
      end


      // state used to request a refill
      REQ_REFILL: 
      begin
         fetch_req_int      = 1'b1;
         fetch_addr_int     = fetch_addr_Q;

         clear_pipe         = fetch_gnt_int;

         if(&way_valid_Q) // all the lines are valid, invalidate one random line
         begin
               fetch_way_int = random_way;
               update_lfsr = 1'b1;
         end
         else
         begin
               fetch_way_int = first_available_way_OH;
               update_lfsr = 1'b0;
         end


         if(fetch_gnt_int)
         begin
            NS = OPERATIVE;
            fetch_rvalid_o  = 1'b1;
         end
         else
         begin
            NS = REQ_REFILL;
         end

      end



      default: 
      begin
        NS = DISABLED_ICACHE;
      end


   endcase // CS
end

   //////////////////////////////////////
   // ██╗     ███████╗███████╗██████╗  //
   // ██║     ██╔════╝██╔════╝██╔══██╗ //
   // ██║     █████╗  ███████╗██████╔╝ //
   // ██║     ██╔══╝  ╚════██║██╔══██╗ //
   // ███████╗██║     ███████║██║  ██║ //
   // ╚══════╝╚═╝     ╚══════╝╚═╝  ╚═╝ //
   //////////////////////////////////////
   generic_LFSR_8bit
   #(
      .OH_WIDTH ( NB_WAYS ),
      .SEED     ( 0       )
   )
   i_LFSR_Way_Repl
   (
      .data_OH_o      ( random_way  ), 
      .data_BIN_o     (             ),
      .enable_i       ( update_lfsr ),      
      .clk            ( clk         ),           
      .rst_n          ( rst_n       )
   );



   // Combinationa logic used to find the first available cache line (not valid)
   // this helps to allocate cache lines in a systematic way
   always_comb
   begin
      first_available_way = 0;

      for(index=0;index<NB_WAYS;index++)
      begin
         if(way_valid_Q[index]==0)
            first_available_way=index;
      end


      HIT_WAY = 0;

      for(index=0;index<NB_WAYS;index++)
      begin
         if(way_match[index]==1)
            HIT_WAY=index;
      end

   end

   // Logic to generate the binary representation of one hot signals
   onehot_to_bin #( .ONEHOT_WIDTH(NB_WAYS) ) WAY_MATCH_BIN (.onehot(way_match), .bin(way_match_bin[ $clog2(NB_WAYS)-1:0]) );
   assign way_match_bin[NB_WAYS-1:$clog2(NB_WAYS)] = 0;

endmodule // icache_top
