// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


`define log2_size(VALUE)    ((VALUE) <= ( 1 ) ? 1 : (VALUE) < ( 2 ) ? 1 : (VALUE) < ( 4 ) ? 2 : (VALUE)< (8) ? 3:(VALUE) < ( 16 )  ? 4 : 5 )
`define FEATURE_ICACHE_STAT

`define FROM_PIPE         1'b0
`define FROM_FIFO         1'b1

module share_icache_controller
#(
   parameter SET_ASSOCIATIVE        = 1,
   parameter CACHE_LINE             = 4,          // WORDS in each cache line allowed value are 1 - 2 - 4 - 8
   parameter CACHE_SIZE             = 4096,        // In Byte
   parameter N_BANKS                = 4,

   parameter AXI_ADDR               = 32,
   parameter AXI_DATA               = 64,
   parameter AXI_ID                 = 10,
   parameter AXI_USER               = 6,

   parameter ICACHE_DATA_WIDTH      = 32,
   parameter ICACHE_ID_WIDTH        = 4,
   parameter ICACHE_ADDR_WIDTH      = 32,

   parameter TAGRAM_DATA_WIDTH      = 10,
   parameter DATARAM_ADDR_WIDTH     = 8,
   parameter DATARAM_DATA_WIDTH     = ICACHE_DATA_WIDTH*CACHE_LINE,
   parameter DATARAM_BE_WIDTH       = DATARAM_DATA_WIDTH/8,
   parameter logic [AXI_ID-1:0] CACHE_ID = 1,
   parameter TAGRAM_ADDR_WIDTH      = $clog2( CACHE_SIZE*8/(SET_ASSOCIATIVE*DATARAM_DATA_WIDTH) ),

   parameter DIRECT_MAPPED_FEATURE  = "ENABLED",
   parameter USE_REDUCED_TAG        = "TRUE",
   parameter REDUCE_TAG_WIDTH       = 10
)
(
   // ---------------------------------------------------------------------------------
   // I/O Port Declarations -----------------------------------------------------------
   // ---------------------------------------------------------------------------------
   input logic                                                         clk,
   input logic                                                         rst_n,
   input logic                                                         test_en_i,

   // ----------------------------------------------------------------------------------
   // SHARED_ICACHE_INTERCONNECT Port Declarations -------------------------------------
   // ----------------------------------------------------------------------------------
   input  logic                                                         fetch_req_i,
   output logic                                                         fetch_grant_o,
   input  logic [ICACHE_ADDR_WIDTH-1:0]                                 fetch_addr_i,
   input  logic [ICACHE_ID_WIDTH-1:0]                                   fetch_ID_i,

   output logic [ICACHE_DATA_WIDTH-1:0]                                 fetch_r_rdata_o,
   output logic                                                         fetch_r_valid_o,
   output logic [ICACHE_ID_WIDTH-1:0]                                   fetch_r_ID_o,


   // Signals connected to tagram
   output logic [TAGRAM_ADDR_WIDTH-1:0]                                 TAG_addr_o,
   output logic [SET_ASSOCIATIVE-1:0]                                   TAG_req_o,
   output logic                                                         TAG_write_o,
   output logic [TAGRAM_DATA_WIDTH-1:0]                                 TAG_wdata_o,
   input  logic [SET_ASSOCIATIVE-1:0] [TAGRAM_DATA_WIDTH-1:0]           TAG_rdata_i,

   // Signals connected to dataram
   output logic [DATARAM_ADDR_WIDTH-1:0]                                DATA_addr_o,
   output logic [SET_ASSOCIATIVE-1:0]                                   DATA_req_o,
   output logic                                                         DATA_write_o,
   output logic [DATARAM_DATA_WIDTH-1:0]                                DATA_wdata_o,
   output logic [DATARAM_BE_WIDTH-1:0]                                  DATA_be_o,
   input  logic [CACHE_LINE-1:0][ICACHE_DATA_WIDTH-1:0]                 DATA_rdata_i,

   output logic [$clog2(SET_ASSOCIATIVE)-1:0]                           DATA_way_muxsel_o, // Used only Whrn N_WAY > 1, no direct mapped

   output logic                                                         bypass_icache_o,

   // ---------------------------------------------------------------
   // AXI4 MASTER Port Declaration----------------------------------
   // ---------------------------------------------------------------
   //AXI read address bus -------------------------------------------
   output  logic [AXI_ID-1:0]                                           init_arid_o,
   output  logic [AXI_ADDR-1:0]                                         init_araddr_o,
   output  logic [ 7:0]                                                 init_arlen_o,
   output  logic [ 2:0]                                                 init_arsize_o,
   output  logic [ 1:0]                                                 init_arburst_o,
   output  logic                                                        init_arlock_o,
   output  logic [ 3:0]                                                 init_arcache_o,
   output  logic [ 2:0]                                                 init_arprot_o,
   output  logic [ 3:0]                                                 init_arregion_o,
   output  logic [ AXI_USER-1:0]                                        init_aruser_o,
   output  logic [ 3:0]                                                 init_arqos_o,
   output  logic                                                        init_arvalid_o,
   input logic                                                          init_arready_i,

   //AXI BACKWARD read data bus ----------------------------------------------
   input  logic [AXI_ID-1:0]                                            init_rid_i,
   input  logic [CACHE_LINE-1:0][ICACHE_DATA_WIDTH-1:0]                 init_rdata_i,
   input  logic [ 1:0]                                                  init_rresp_i,
   input  logic [ AXI_USER-1:0]                                         init_ruser_i,
   input  logic                                                         init_rvalid_i,
   output logic                                                         init_rready_o,

   // Control ports
   input  logic                                                         ctrl_req_enable_icache_i,
   output logic                                                         ctrl_ack_enable_icache_o,

   input  logic                                                         ctrl_req_disable_icache_i,
   output logic                                                         ctrl_ack_disable_icache_o,

   input  logic                                                         ctrl_req_flush_icache_i,
   output logic                                                         ctrl_ack_flush_icache_o,

   output logic                                                         ctrl_pending_trans_icache_o,

   input  logic                                                         ctrl_sel_flush_req_i,
   input  logic [31:0]                                                  ctrl_sel_flush_addr_i,
   output logic                                                         ctrl_sel_flush_ack_o

   `ifdef FEATURE_ICACHE_STAT
   ,
   output logic [31:0]                                                  ctrl_hit_count_icache_o,
   output logic [31:0]                                                  ctrl_trans_count_icache_o,
   output logic [31:0]                                                  ctrl_miss_count_icache_o,
   input  logic                                                         ctrl_clear_regs_icache_i,
   input  logic                                                         ctrl_enable_regs_icache_i
   `endif
);


    //LOCAL PARAMETERS
    localparam  N_ROWS        = 2**TAGRAM_ADDR_WIDTH;
    localparam  OFFSET_BIT    = $clog2(ICACHE_DATA_WIDTH/8);

    localparam  INDEX_LSB_SH  =                     $clog2(N_BANKS) + $clog2(CACHE_LINE) + OFFSET_BIT ;
    localparam  INDEX_MSB_SH  = TAGRAM_ADDR_WIDTH + $clog2(N_BANKS) + $clog2(CACHE_LINE) + OFFSET_BIT -1 ;

    localparam  INDEX_LSB_PRI =                   + $clog2(CACHE_LINE) + OFFSET_BIT ;
    localparam  INDEX_MSB_PRI = TAGRAM_ADDR_WIDTH + $clog2(CACHE_LINE) + OFFSET_BIT -1 ;


    localparam  TAG_LSB_SH    = TAGRAM_ADDR_WIDTH + $clog2(N_BANKS) + $clog2(CACHE_LINE) + OFFSET_BIT;
    localparam  TAG_LSB_PRI   = TAGRAM_ADDR_WIDTH                   + $clog2(CACHE_LINE) + OFFSET_BIT;

    localparam  TAG_MSB_PRI   = (USE_REDUCED_TAG == "TRUE") ?   (TAG_LSB_PRI + REDUCE_TAG_WIDTH-1 + $clog2(N_BANKS))    :    (ICACHE_ADDR_WIDTH-1);
    localparam  TAG_MSB_SH    = (USE_REDUCED_TAG == "TRUE") ?   (TAG_LSB_SH  + REDUCE_TAG_WIDTH-1)                      :    (ICACHE_ADDR_WIDTH-1);


    integer i;

   enum logic [3:0]                {   DISABLED_ICACHE,
                                       WAIT_EMPTYING_DIS_ICACHE,
                                       INVALIDATE,
                                       OPERATIVE_STATE,
                                       REQUEST_A_REFILL,
                                       SERVE_REFILL,
                                       WAIT_CRITICAL_REFILL,
                                       SERVE_CRITICAL_REFILL,
                                       SERVE_CRITICAL_REFILL_2,
                                       DISPATCH_CRITICAL_1,
                                       DISPATCH_CRITICAL_2,
                                       DO_SEL_FLUSH
                                    } CS, NS;

    // FIFO USED TO STORE PENDING REFILL infos
    logic                                                 push_refill_info;
    logic                                                 pop_refill_info;
    logic                                                 valid_refill_info;
    logic                                                 fifo_not_full;
    logic [SET_ASSOCIATIVE-1:0]                           way_to_refill;
    logic [TAGRAM_ADDR_WIDTH-1:0]                         index_to_refill;
    logic [TAGRAM_DATA_WIDTH-2:0]                         tag_to_refill;

    logic [ICACHE_ID_WIDTH-1:0]                           fetch_ID_to_refill;

    logic                                                 fetch_req  [2:0];
    logic [ICACHE_ADDR_WIDTH-1:0]                         fetch_addr [2:0];
    logic [ICACHE_ID_WIDTH-1:0]                           fetch_ID   [2:0];

    // if (fetch_req[0] == 1) then if hit[0] == 1  --> HIT, if hit[0] == 0 --> MISS
    logic                                                 hit        [2:1];
    logic [TAGRAM_ADDR_WIDTH-1:0]                         index      [2:1];
    logic [TAGRAM_DATA_WIDTH-2:0]                         tag        [2:1];

    logic [`log2_size(CACHE_LINE-1)-1:0]                  word_offset [2:1];
    logic [`log2_size(CACHE_LINE-1)-1:0]                  word_offset_to_refill;

    logic [SET_ASSOCIATIVE-1:0]                           match_S1;
    logic [SET_ASSOCIATIVE-1:0]                           valid_cache_line_S1;

    //--------------------------------------------------------------------------------//
    //USED ONLY IF DIRECT_MAPPED_FEATURE is ENABLED
    logic                                                 enable_LFSR;
    logic [SET_ASSOCIATIVE-1:0]                           way_to_replace_OH_S2;
    logic [$clog2(SET_ASSOCIATIVE)-1:0]                   way_to_replace_BIN_S2;
    //--------------------------------------------------------------------------------//

    logic [TAGRAM_ADDR_WIDTH-1:0]                        CounterINV, CounterINV_next;
    logic                                                enable_pipeline;
    logic                                                clear_pipeline;

    logic                                                FetchIsUnderRefill;

    logic                                                sel_rdata_int;

    logic [ICACHE_DATA_WIDTH-1:0]                        fetch_r_rdata_int;


    // ALIGN ADDR FIFO signals: when cache is disabled are used to select the 32bit data chunk (over 64 bit data)
    logic                                                pop_align_addr;    // pop from fifo
    logic                                                valid_align_addr;  // FIFO is not empty
    logic                                                alig_addr_muxsel;
    logic                                                fifo_align_addr_gnt; // grant for push side align fifo
    logic [ICACHE_ID_WIDTH-1:0]                          fetch_ID_int;

    logic [TAGRAM_ADDR_WIDTH + TAG_MSB_PRI-TAG_LSB_PRI : 0] RESP_check_ID_int;

`ifdef FEATURE_ICACHE_STAT
    logic                                                incr_hit_count;
    logic                                                incr_trans_count;
    logic                                                incr_miss_count;
`endif

    // ------------------------------------------------------------------------//
    //                        CODE STARTS HERE !!!!!!!!!!!!!
    // ------------------------------------------------------------------------//

 `ifdef FEATURE_ICACHE_STAT
      always_ff @(posedge clk, negedge rst_n)
      begin
        if( rst_n == 1'b0)
        begin
              ctrl_hit_count_icache_o    <= '0;
              ctrl_trans_count_icache_o  <= '0;
              ctrl_miss_count_icache_o   <= '0;
        end
        else
        begin
              if(ctrl_clear_regs_icache_i) // clear all the registers
              begin
                  ctrl_hit_count_icache_o    <= '0;
                  ctrl_trans_count_icache_o  <= '0;
                  ctrl_miss_count_icache_o   <= '0;
              end
              else
              begin
                  if(ctrl_enable_regs_icache_i) // if regs are enabled, then update
                  begin
                    if(incr_hit_count)
                      ctrl_hit_count_icache_o <= ctrl_hit_count_icache_o + 1'b1;

                    if(incr_trans_count)
                      ctrl_trans_count_icache_o <= ctrl_trans_count_icache_o + 1'b1;

                    if(incr_miss_count)
                      ctrl_miss_count_icache_o   <= ctrl_miss_count_icache_o + 1'b1;
                  end
              end

        end
      end
`endif




    assign bypass_icache_o = (CS == DISABLED_ICACHE) || ( CS == WAIT_EMPTYING_DIS_ICACHE) || (CS == INVALIDATE);

    assign ctrl_pending_trans_icache_o = valid_refill_info | valid_align_addr; //There are pending transaction both when cache is enabled (pending refill) or cache is disbalde but there are in fligth responses

    // BCAST GRANULARITY == 1'b1;
    always_comb
    begin
      if ( (CS == DISABLED_ICACHE) || (CS == WAIT_EMPTYING_DIS_ICACHE) )
      begin
            fetch_r_rdata_o = fetch_r_rdata_int;
      end
      else // Cache is enabled
      begin
            if(sel_rdata_int == `FROM_PIPE)
              fetch_r_rdata_o =  DATA_rdata_i[word_offset[1]];
            else //FROM_FIFO
              fetch_r_rdata_o =  init_rdata_i[word_offset_to_refill];
      end
    end


    generate



        assign index[1]       =  fetch_addr[1][ INDEX_MSB_SH : INDEX_LSB_SH ];
        assign tag[1]         =  fetch_addr[1][ TAG_MSB_SH   : TAG_LSB_SH   ];

        case(CACHE_LINE)
        1: begin
            assign word_offset[1] = 1'b0;
        end

        2: begin
         assign word_offset[1] = fetch_addr[1][OFFSET_BIT];
        end

        default : begin
          assign word_offset[1] = fetch_addr[1][$clog2(CACHE_LINE)+OFFSET_BIT-1:OFFSET_BIT];
        end
        endcase
    endgenerate


    assign fetch_req[0]   = fetch_req_i;
    assign fetch_addr[0]  = fetch_addr_i;
    assign fetch_ID[0]    = fetch_ID_i;

    // CHECH THE MATCH and VALID lines
    always_comb
    begin
        for(i=0; i<SET_ASSOCIATIVE; i++)
        begin
            valid_cache_line_S1[i]  =    TAG_rdata_i[i][TAGRAM_DATA_WIDTH-1];
            match_S1[i]             =   (TAG_rdata_i[i][TAGRAM_DATA_WIDTH-2:0] == tag[1]) &&  (TAG_rdata_i[i][TAGRAM_DATA_WIDTH-1] == 1'b1);

        end
    end

    assign hit[1] = |match_S1;



    // UPDATE COUNTERS AND CURRENT STATE
    always_ff @(posedge clk, negedge rst_n)
    begin
        if(rst_n == 1'b0)
        begin
            CS                     <= DISABLED_ICACHE;
            CounterINV             <= '0;

            fetch_req  [2]         <= 1'b0;
            fetch_req  [1]         <= 1'b0;
            fetch_addr [2]         <= '0;
            fetch_addr [1]         <= '0;
            fetch_ID   [2]         <= '0;
            fetch_ID   [1]         <= '0;

            hit        [2]         <= '0;
            index      [2]         <= '0;
            word_offset[2]         <= '0;

        end
        else
        begin
            CS            <= NS;

            if(CS == INVALIDATE)
              CounterINV <= CounterINV_next;


            if(clear_pipeline)
            begin
                fetch_req  [2]         <= 1'b0;
                fetch_req  [1]         <= 1'b0;
                fetch_addr [2]         <= '0;
                fetch_addr [1]         <= '0;
                fetch_ID   [2]         <= '0;
                fetch_ID   [1]         <= '0;
                hit        [2]         <= '0;
                index      [2]         <= '0;
                word_offset[2]         <= '0;
            end
            else  if(enable_pipeline)
                  begin
                      fetch_req  [2]   <= fetch_req  [1];
                      fetch_req  [1]   <= fetch_req  [0];

                      fetch_addr [2:1] <= fetch_addr [1:0];
                      fetch_ID   [2:1] <= fetch_ID   [1:0];
                      hit        [2]   <= hit          [1];
                      index      [2]   <= index        [1];
                      word_offset[2]   <= word_offset  [1];
                  end
        end
    end


`ifdef FEATURE_ICACHE_STAT
      assign incr_trans_count            = fetch_req_i & fetch_grant_o;
      assign incr_miss_count             = init_arvalid_o & init_arready_i & ( CS == REQUEST_A_REFILL );
`endif
    // UPDATE NS and OUTPUTS
    always_comb
    begin
        // Default outputs
        CounterINV_next  = CounterINV;
        enable_pipeline  = 1'b0;
        enable_LFSR      = 1'b0;

        clear_pipeline   = 1'b0;

        // LOG INTECO SHARED I-CACHE
        fetch_r_ID_o      = fetch_ID[1]; // take it from STAGE_1
        fetch_r_valid_o   = 1'b0;
        fetch_grant_o     = 1'b0;
        fetch_r_rdata_int = '0;
        sel_rdata_int     = `FROM_PIPE;

        // AXI AR REQUEST REFILL
        init_arvalid_o   = 1'b0;
        init_arid_o      = CACHE_ID;
        init_arlock_o    = 1'b0;
        init_arcache_o   = '0;
        init_arprot_o    = '0;
        init_arregion_o  = '0;
        init_aruser_o    = '0; // NOT USED
        init_arqos_o     = '0;

        init_arsize_o    = 3'b011;  // AXI4 datawidth is 64bit --> 8 bytes
        init_arburst_o   = 2'b01;   // INCR

        init_rready_o       = 1'b0;

        //Control ports
        ctrl_ack_enable_icache_o  = 1'b0;
        ctrl_ack_disable_icache_o = 1'b0;
        ctrl_ack_flush_icache_o   = 1'b0;
        ctrl_sel_flush_ack_o      = 1'b0;

        pop_align_addr            = 1'b0;

`ifdef FEATURE_ICACHE_STAT
      incr_hit_count              = 1'b0;
`endif

        case(ICACHE_DATA_WIDTH)
        32:
        begin
                case(CACHE_LINE) //FIXME OK for 64 bit data AXI
                1:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:2],2'b00};       end
                2:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:3],3'b000};      end
                4:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:4],4'b0000};     end
                8:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:5],5'b00000};    end
                16:      begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:6],6'b000000};   end
                32:      begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:7],7'b0000000};  end
                default: begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:2],2'b00};       end
                endcase
        end

        64:
        begin
                case(CACHE_LINE) //FIXME OK for 64 bit data AXI
                1:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:3],3'b000};      end
                2:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:4],4'b0000};     end
                4:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:5],5'b00000};    end
                8:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:6],6'b000000};   end
                16:      begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:7],7'b0000000};  end
                default: begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:3],3'b000};       end
                endcase
        end

        128:
        begin
                case(CACHE_LINE) //FIXME OK for 64 bit data AXI
                1:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:4],4'b0000};     end
                2:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:5],5'b00000};    end
                4:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:6],6'b000000};   end
                8:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:7],7'b0000000};  end
                default: begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:4],4'b0000};     end
                endcase
        end

        256:
        begin
                case(CACHE_LINE) //FIXME OK for 64 bit data AXI
                1:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:5],5'b00000};     end
                2:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:6],6'b000000};    end
                4:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:7],7'b0000000};   end
                8:       begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:8],8'b00000000};  end
                default: begin  init_araddr_o   = {fetch_addr[1][ICACHE_ADDR_WIDTH-1:5],5'b00000};     end
                endcase
        end

        endcase


        init_arlen_o     =  (CACHE_LINE*ICACHE_DATA_WIDTH)/AXI_DATA - 1;

        // FIFO used to store info about Pending refills
        push_refill_info = 1'b0;
        pop_refill_info  = 1'b0;
        enable_LFSR      = 1'b0;

        // Default values for TAGRAM - DATARAM


        TAG_addr_o       =  fetch_addr[0][INDEX_MSB_SH:INDEX_LSB_SH];
        TAG_req_o        =  '0; // write in parallel to all the memories
        TAG_write_o      =  1'b0;
        TAG_wdata_o      =  '0;  // set to zero the MSB


        DATA_addr_o      =  fetch_addr[0][INDEX_MSB_SH:INDEX_LSB_SH];
        DATA_req_o       =   '0;
        DATA_be_o        =   '0;
        DATA_wdata_o     =   '0;
        DATA_write_o     =   1'b0;

        // CASE OF THE MAIN FINITE STATE MACHINE
        case(CS)

            DISABLED_ICACHE:
            begin
                ctrl_ack_disable_icache_o = 1'b1;
                ctrl_ack_flush_icache_o   = 1'b1;
                ctrl_sel_flush_ack_o      = 1'b1;
                ctrl_ack_enable_icache_o  = 1'b0;

                clear_pipeline            = 1'b1;
                case(ICACHE_DATA_WIDTH)
                  32:    begin init_araddr_o = {fetch_addr_i[31:3],    3'b000 };   init_arlen_o = 8'h00; end // DO ALIGNED ACCESS on 64bit
                  64:    begin init_araddr_o = {fetch_addr_i[31:3],    3'b000 };   init_arlen_o = 8'h00; end
                  128:   begin init_araddr_o = {fetch_addr_i[31:4],   4'b0000 };   init_arlen_o = 8'h01; end
                  256:   begin init_araddr_o = {fetch_addr_i[31:5],  5'b00000 };   init_arlen_o = 8'h03; end
                  512:   begin init_araddr_o = {fetch_addr_i[31:6], 6'b000000 };   init_arlen_o = 8'h07; end
                endcase

                // AXI AR REQUEST REFILL
                //init_aruser_o       = fetch_ID_i; // Just for Debug
                init_arlock_o       = 1'b0;
                init_arsize_o       = 3'b011;  // AXI4 datawidth is 32bit --> 4 bytes
                init_arburst_o      = 2'b01;   // INCR
                init_arvalid_o      = fetch_req_i & fifo_align_addr_gnt; //Store  the fetch ID in the FIFO ALIGN

                // always allow the L2 to deliver responses
                init_rready_o       = 1'b1;
                fetch_r_rdata_int   = init_rdata_i[0];
                fetch_r_ID_o        = fetch_ID_int;

                //POP align address information in case there is a valid response
                if(init_rvalid_i)
                begin
                  pop_align_addr      = 1'b1;
                  fetch_r_valid_o     = 1'b1;
                end
                else
                begin
                  pop_align_addr      = 1'b0;
                  fetch_r_valid_o     = 1'b0;
                end


                if(ctrl_req_disable_icache_i)
                begin
                    fetch_grant_o             = init_arready_i & fifo_align_addr_gnt;
                    NS                        = DISABLED_ICACHE;
                    init_arvalid_o            = fetch_req_i & fifo_align_addr_gnt; // make a request only if we can track it
                end
                else //~ ctrl_req_disable_icache_i == 1'b0
                begin
                    if(ctrl_req_enable_icache_i) //--> Invalidate the cache
                    begin
                      NS                  = WAIT_EMPTYING_DIS_ICACHE;
                      fetch_grant_o       = 1'b0;
                      init_arvalid_o      = 1'b0;
                    end
                    else
                    begin
                      fetch_grant_o       = init_arready_i & fifo_align_addr_gnt;
                      NS                  = DISABLED_ICACHE;
                      init_arvalid_o      = fetch_req_i & fifo_align_addr_gnt; // make a request only if we can track it
                    end
                end

            end //~DISABLED_ICACHE



            WAIT_EMPTYING_DIS_ICACHE :
            begin

                fetch_grant_o       = 1'b0;
                fetch_r_rdata_int   = init_rdata_i[0];
                fetch_r_ID_o        = fetch_ID_int;

                // always allow the L2 to deliver responses
                init_rready_o       = 1'b1;

                if(init_rvalid_i)
                begin
                  pop_align_addr      = 1'b1;
                  fetch_r_valid_o     = 1'b1;
                end
                else
                begin
                  pop_align_addr      = 1'b0;
                  fetch_r_valid_o     = 1'b0;
                end




                if(valid_align_addr == 1'b0)
                begin
                  NS = INVALIDATE;
                  ctrl_ack_enable_icache_o = 1'b1;
                end
                else
                begin
                  NS = WAIT_EMPTYING_DIS_ICACHE;
                end

            end

            INVALIDATE:
            begin
                fetch_grant_o    = 1'b0;
                clear_pipeline   = 1'b1;

                // TAGRAM SIGNALS
                TAG_addr_o       =  CounterINV;
                TAG_req_o        =  '1; // write in parallel to all the memories
                TAG_write_o      =  1'b1;
                TAG_wdata_o[TAGRAM_DATA_WIDTH-1]     =  '0;  // set to zero the MSB

                if(CounterINV != N_ROWS-1)
                begin
                    CounterINV_next  = CounterINV + 1'b1;
                    NS               = INVALIDATE;
                end
                else
                begin
                    ctrl_ack_flush_icache_o = 1'b1;

                    CounterINV_next = '0;
                    if(ctrl_req_disable_icache_i)
                      NS = DISABLED_ICACHE;
                    else
                      NS = OPERATIVE_STATE;
                end

            end //~INVALIDATE

            DO_SEL_FLUSH:
            begin
               fetch_grant_o    = 1'b0;
               clear_pipeline   = 1'b1;

               TAG_addr_o =  ctrl_sel_flush_addr_i[INDEX_MSB_SH : INDEX_LSB_SH];
               TAG_req_o   =  '1;
               TAG_write_o =  1'b1;
               TAG_wdata_o[TAGRAM_DATA_WIDTH-1]  =  '0;  // set to zero the MSB

                NS = OPERATIVE_STATE;
                ctrl_sel_flush_ack_o = 1'b1;
            end


            OPERATIVE_STATE:
            begin

                if(init_rvalid_i) // serve the response
                begin
                    init_rready_o      = 1'b0;
                    enable_pipeline    = 1'b0;
                    fetch_grant_o      = 1'b0;

                    if(FetchIsUnderRefill)
                    begin
                          NS                    = SERVE_CRITICAL_REFILL;
                    end
                    else
                    begin
                          NS                    = SERVE_REFILL;

                          //if there is a pending HIT, serve it in parallel, ,then clear the pipe.
                          // STAGE 1
                          if(fetch_req[1] & hit[1] ) // there is a valid request on stage_1 of the pipe
                          begin

                        `ifdef FEATURE_ICACHE_STAT
                            incr_hit_count    = 1'b1;
                        `endif
                            fetch_r_valid_o   = 1'b1;
                            fetch_r_ID_o      = fetch_ID[1];

                            sel_rdata_int         =`FROM_PIPE;

                            clear_pipeline    = 1'b1;
                          end
                    end

                end
                else  //~if(init_r_req_i) no incoming response then use the pipe
                begin

                    if(ctrl_req_enable_icache_i)
                    begin
                              ctrl_ack_enable_icache_o = 1'b1;
                              TAG_req_o        =  {SET_ASSOCIATIVE{fetch_req[0]}}; // read in parallel to all the memories
                              DATA_req_o       =  {SET_ASSOCIATIVE{fetch_req[0]}};
                    end
                    else
                    begin
                          if(ctrl_req_disable_icache_i)  // do not push transaction inside the pipe if there are request to disable the cache
                          begin
                              TAG_req_o        =  {SET_ASSOCIATIVE{1'b0}}; // read in parallel to all the memories
                              DATA_req_o       =  {SET_ASSOCIATIVE{1'b0}};
                          end
                          else
                          begin
                              TAG_req_o        =  {SET_ASSOCIATIVE{fetch_req[0]}}; // read in parallel to all the memories
                              DATA_req_o       =  {SET_ASSOCIATIVE{fetch_req[0]}};
                          end
                    end

                    // STAGE 0
                    TAG_addr_o      =  fetch_addr[0][INDEX_MSB_SH:INDEX_LSB_SH];
                    DATA_addr_o     =  fetch_addr[0][INDEX_MSB_SH:INDEX_LSB_SH];

                    TAG_write_o      =  1'b0;


                    TAG_wdata_o[TAGRAM_DATA_WIDTH-1]  =  '0;  // set to zero the MSB
                    DATA_write_o                      =  1'b0;

                    // STAGE 1
                    if(fetch_req[1]) // there is a valid request on stage_1 of the pipe
                    begin

                        if(hit[1]) // There is a hit
                        begin
                         `ifdef FEATURE_ICACHE_STAT
                              incr_hit_count    = 1'b1;
                        `endif
                              fetch_r_valid_o     = 1'b1;
                              fetch_r_ID_o        = fetch_ID[1];
                              NS                  = OPERATIVE_STATE;

                              sel_rdata_int       = `FROM_PIPE; //-->Select FROM STAGE 1

                              // Request to disable the cache --> DONT grant any incoming transaction
                              if(ctrl_req_disable_icache_i | ctrl_req_flush_icache_i | ctrl_sel_flush_req_i )
                              begin
                                fetch_grant_o       = 1'b0;

                                 if(ctrl_req_disable_icache_i)
                                   begin
                                      NS          = DISABLED_ICACHE;
                                   end
                                 else if(ctrl_sel_flush_req_i)
                                   NS = DO_SEL_FLUSH;
                                 else
                                   NS = INVALIDATE;  // we are here because one of the 3 ctrl signal is one
                              end
                              else
                              begin
                                fetch_grant_o       = 1'b1;
                              end

                              enable_pipeline     = 1'b1;

                        end
                        else // There is a miss
                        begin
                              enable_pipeline = 1'b0;
                              fetch_grant_o   = 1'b0;

                              //FIXME --> OK there is a miss, first I check if there is a pending refill at the same cache line address
                              if(FetchIsUnderRefill)
                                  begin
                                        NS = WAIT_CRITICAL_REFILL; // Stay here untill the refill comes
                                  end
                              else // There are no pending refill at this address addr[1], so if FIFO_Req is not full, te refill is sent to the REFILL port
                                  begin
                                            NS = REQUEST_A_REFILL;
                                  end


                        end

                    end
                    else  // There are no pending request on stage 1
                    begin


                             if(ctrl_req_disable_icache_i | ctrl_sel_flush_req_i | ctrl_req_flush_icache_i)
                             begin
                                   fetch_grant_o      = 1'b0;
                                   enable_pipeline    = 1'b0;

                                   if(valid_refill_info == 1'b1)
                                   begin
                                       NS             = WAIT_CRITICAL_REFILL; //OPERATIVE_STATE;
                                   end
                                   else
                                   begin
                                       if(ctrl_req_disable_icache_i)
                                       begin
                                          NS          = DISABLED_ICACHE;
                                       end
                                       else if(ctrl_sel_flush_req_i)
                                               NS = DO_SEL_FLUSH;
                                            else
                                               NS = INVALIDATE;  // we are here because one of the 3 ctrl signal is one
                                   end
                             end
                             else
                             begin
                                 fetch_grant_o      = 1'b1;
                                 NS                 = OPERATIVE_STATE;
                                 enable_pipeline    = 1'b1;
                             end


                    end

                end
            end //~OPERATIVE_STATE





            WAIT_CRITICAL_REFILL :
            begin
                enable_pipeline = 1'b0;
                fetch_grant_o   = 1'b0;
                init_rready_o   = 1'b0;

                if(init_rvalid_i) // serve the response
                begin
                    NS                      = SERVE_CRITICAL_REFILL;
                end
                else
                begin
                    NS                      = WAIT_CRITICAL_REFILL;
                end

            end //~WAIT_CRITICAL_REFILL





            SERVE_CRITICAL_REFILL:
            begin
                    init_rready_o     = 1'b1;
                    pop_refill_info   = 1'b1;

                    enable_pipeline  = 1'b0;

                    // TAGRAM UPDATE THE TAG --> Just Fist STBUS RESPONSE TRANSFER
                    TAG_addr_o       =  index_to_refill ;
                    TAG_req_o        =  way_to_refill; // write in parallel to all the memories
                    TAG_write_o      =  1'b1;
                    TAG_wdata_o      =  {1'b1,tag_to_refill};  // set to one the MSB

                    // DATARAM UPDATE THE DATA
                    DATA_addr_o      =  index_to_refill;
                    DATA_req_o       =  way_to_refill;
                    DATA_write_o     =  1'b1;
                    DATA_be_o        =  '1;
                    DATA_wdata_o     =  init_rdata_i;

                    sel_rdata_int     = `FROM_FIFO;

                    fetch_r_valid_o  = 1'b1;
                    fetch_r_ID_o     = fetch_ID_to_refill;

                    NS = DISPATCH_CRITICAL_1;
            end //~SERVE_CRITICAL_REFILL




            DISPATCH_CRITICAL_1 :
            begin

                if(FetchIsUnderRefill == 1'b0)
                begin

                    TAG_addr_o       =  fetch_addr[1][INDEX_MSB_SH:INDEX_LSB_SH];
                    TAG_req_o        =  {SET_ASSOCIATIVE{fetch_req[1]}}; // read in parallel to all the memories
                    TAG_write_o      =  1'b0;
                    TAG_wdata_o[TAGRAM_DATA_WIDTH-1]     =  '0;  // set to zero the MSB

                    DATA_addr_o      =  fetch_addr[1][INDEX_MSB_SH:INDEX_LSB_SH];
                    DATA_req_o       =  {SET_ASSOCIATIVE{fetch_req[1]}};
                    DATA_write_o     =  1'b0;
                    DATA_be_o        =  '0;
                    DATA_wdata_o     =  '0;

                    NS = DISPATCH_CRITICAL_2;
                end
                else
                begin
                    NS = WAIT_CRITICAL_REFILL;
                end
            end //~DISPATCH_CRITICAL


            DISPATCH_CRITICAL_2 :
            begin
              `ifdef FEATURE_ICACHE_STAT
                    incr_hit_count    = 1'b1;
              `endif
                    clear_pipeline    = 1'b1;

                    fetch_r_valid_o   = 1'b1;
                    fetch_r_ID_o      = fetch_ID[1];
                    NS                = OPERATIVE_STATE;

                    sel_rdata_int     = `FROM_PIPE;

                    NS = OPERATIVE_STATE;

            end //~DISPATCH_CRITICAL





            REQUEST_A_REFILL:
            begin

              if(init_rvalid_i) // serve the response first
              begin

                    NS                      = SERVE_CRITICAL_REFILL_2;

              end //~if(init_r_req_i) no incoming response then use the pipe
              else
              begin
                    init_arvalid_o    = fifo_not_full;
                    //init_aruser_o     = fetch_ID[1];
                    fetch_grant_o     = 1'b0;

                    if(init_arready_i & fifo_not_full)
                    begin
                        NS = OPERATIVE_STATE;
                        push_refill_info  = 1'b1;
                    `ifndef DIRECT_MAPPED
                        enable_LFSR       = 1'b1;
                    `endif
                        clear_pipeline    = 1'b1;
                    end
                    else
                    begin
                        NS = REQUEST_A_REFILL;
                    end
              end

            end //~REQUEST_A_REFILL



           //FIXME IGOR ADDON to fix refill req when previous refill resp arrives
           SERVE_CRITICAL_REFILL_2:
           begin
                    init_rready_o    = 1'b1;
                    pop_refill_info  = 1'b1;

                    enable_pipeline  = 1'b0;

                    // TAGRAM UPDATE THE TAG --> Just Fist AXI RESPONSE TRANSFER
                    TAG_addr_o       =  index_to_refill ;
                    TAG_req_o        =  way_to_refill; // write in parallel to all the memories
                    TAG_write_o      =  1'b1;
                    TAG_wdata_o      =  {1'b1,tag_to_refill} ;  // set to one the MSB

                    // DATARAM UPDATE THE DATA
                    DATA_addr_o      =  index_to_refill;
                    DATA_req_o       =  way_to_refill;
                    DATA_write_o     =  1'b1;
                    DATA_be_o        =  '1;
                    DATA_wdata_o     =  init_rdata_i;

                    sel_rdata_int     =`FROM_FIFO;


                    fetch_r_valid_o  = 1'b1;
                    fetch_r_ID_o     = fetch_ID_to_refill;

                    NS = REQUEST_A_REFILL;
           end //~SERVE_REFILL_CRITICAL



            SERVE_REFILL:
            begin
                    init_rready_o    = 1'b1;
                    pop_refill_info  = 1'b1;

                    enable_pipeline  = 1'b0;

                    // TAGRAM UPDATE THE TAG --> Just Fist STBUS RESPONSE TRANSFER
                    TAG_addr_o      =  index_to_refill ;
                    TAG_req_o        =  way_to_refill; // write in parallel to all the memories
                    TAG_write_o      =  1'b1;
                    TAG_wdata_o      =  {1'b1,tag_to_refill};  // set to one the MSB FIXME

                    // DATARAM UPDATE THE DATA
                    DATA_addr_o      =  index_to_refill;
                    DATA_req_o       =  way_to_refill;
                    DATA_write_o     =  1'b1;
                    DATA_be_o        =  '1;
                    DATA_wdata_o     =  init_rdata_i;

                    sel_rdata_int     =`FROM_FIFO;


                    fetch_r_valid_o  = 1'b1;
                    fetch_r_ID_o     = fetch_ID_to_refill;
                    NS = OPERATIVE_STATE;
            end //~SERVE_REFILL

            default:
            begin
                  NS = DISABLED_ICACHE;
            end //~default
        endcase
    end




  generate
  if(DIRECT_MAPPED_FEATURE == "DISABLED")
  begin : _MULTIWAY_
        onehot_to_bin #( .ONEHOT_WIDTH(SET_ASSOCIATIVE) ) RDATA_MUXSEL_BIN(.onehot(match_S1), .bin(DATA_way_muxsel_o));

        // LSFR to calculate A RANDOM WAY TO PUT THE INCOMING REFILL
        lfsr_8bit
        #(
          .WIDTH(SET_ASSOCIATIVE),
          .SEED(0)
        )
            RANDOM_WAY_REPLACEMENT
        (
            .refill_way_oh(way_to_replace_OH_S2),
            .refill_way_bin(way_to_replace_BIN_S2),
            .en_i(enable_LFSR),
            .clk_i(clk),
            .rst_ni(rst_n)
        );

        generic_fifo
        #(
            .DATA_WIDTH( ICACHE_ID_WIDTH + `log2_size(CACHE_LINE-1) + TAGRAM_DATA_WIDTH-1 + TAGRAM_ADDR_WIDTH + SET_ASSOCIATIVE ),
            .DATA_DEPTH(4)
        )
        ADDRESS_WAY_REFILL_FIFO
        (
            .clk          ( clk                                                                                              ),
            .rst_n        ( rst_n                                                                                            ),
            .test_mode_i  ( test_en_i                                                                                        ),
            .data_i       ( { fetch_ID[1], word_offset[1] , tag[1] , index[1] , way_to_replace_OH_S2 }                       ),
            .valid_i      ( push_refill_info                                                                                 ),
            .grant_o      ( fifo_not_full                                                                                    ),
            .data_o       ( { fetch_ID_to_refill, word_offset_to_refill , tag_to_refill , index_to_refill , way_to_refill }  ),
            .valid_o      ( valid_refill_info                                                                                ),
            .grant_i      ( pop_refill_info                                                                                  )
        );
  end
  else
  begin : _DIRECT_MAPPED_
    generic_fifo
    #(
       .DATA_WIDTH( ICACHE_ID_WIDTH + `log2_size(CACHE_LINE-1) + TAGRAM_DATA_WIDTH-1 + TAGRAM_ADDR_WIDTH + 1 ),
       .DATA_DEPTH(4)
    )
    ADDRESS_WAY_REFILL_FIFO
    (
        .clk          ( clk                                                                                             ),
        .rst_n        ( rst_n                                                                                           ),
        .test_mode_i  ( test_en_i                                                                                       ),
        .data_i       ( { fetch_ID[1], word_offset[1] , tag[1] , index[1] , 1'b1 }                                      ),  // DIRECT MAPPED ONLY ONE WAY to be refilled
        .valid_i      ( push_refill_info                                                                                ),
        .grant_o      ( fifo_not_full                                                                                   ),
        .data_o       ( { fetch_ID_to_refill, word_offset_to_refill , tag_to_refill , index_to_refill , way_to_refill } ),
        .valid_o      ( valid_refill_info                                                                               ),
        .grant_i      ( pop_refill_info                                                                                 )
    );
  end




    RefillTracker_4
    #(
        .ID_WIDTH(TAGRAM_ADDR_WIDTH + TAG_MSB_SH-TAG_LSB_SH+1)
    )
    u_RefillTracker
    (
        .clk(clk),
        .rst_n(rst_n),
        //Push side
        .push_i(push_refill_info),
        .push_ID_i({tag[1],index[1]}),
        .push_full_o(), // The generic FIFO full is used and this tracker is synch with the GEN FIFO
        //Pop side
        .pop_i(pop_refill_info),
        .pop_ID_i( {tag_to_refill, index_to_refill}),
        .pop_empty_o(),
        .pop_error_o(),
        //Debug Side
        .RESP_check_ID_i({ fetch_addr[1][TAG_MSB_SH:TAG_LSB_SH], fetch_addr[1][INDEX_MSB_SH:INDEX_LSB_SH]}),     // FIXME .RESP_check_ID_i({fetch_addr[0][INDEX_MSB:INDEX_LSB] , fetch_addr[0][TAG_MSB:TAG_LSB] }),
        .RESP_check_req_i(fetch_req[1]),                                                                          // FIXME .RESP_check_req_i(fetch_req[0]),
        .RESP_check_is_valid_o(FetchIsUnderRefill)
    );

  endgenerate










    generic_fifo
    #(
        .DATA_WIDTH( 1 + ICACHE_ID_WIDTH ),
        .DATA_DEPTH( 4 )
    )
    ADDR_ALIGNMENT_ICACHE_FIFO
    (
        .clk          ( clk       ),
        .rst_n        ( rst_n     ),
        .test_mode_i  ( test_en_i ),
        .data_i       ( {fetch_addr_i[2], fetch_ID_i} ),
        .valid_i      ( fetch_req_i & fetch_grant_o &  ((CS == DISABLED_ICACHE) || (CS == WAIT_EMPTYING_DIS_ICACHE))  ),
        .grant_o      ( fifo_align_addr_gnt ),
        .data_o       ( {alig_addr_muxsel, fetch_ID_int} ),
        .valid_o      ( valid_align_addr ),
        .grant_i      ( pop_align_addr   )
    );

endmodule
