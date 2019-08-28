// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// ============================================================================= //
// Company:        Multitherman Laboratory @ DEIS - University of Bologna        //
//                    Viale Risorgimento 2 40136                                 //
//                    Bologna - fax 0512093785 -                                 //
//                                                                               //
// Engineer:       Igor Loi - igor.loi@unibo.it                                  //
//                                                                               //
// Additional contributions by:                                                  //
//                                                                               //
// Create Date:    18/08/2014                                                    // 
// Design Name:    icache_ctrl_unit                                              // 
// Module Name:    icache_ctrl_unit                                              //
// Project Name:   PULP                                                          //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:    ICACHE control Unit, used to enable/disable icache banks      //
//                 flush operations, and to debug the status og cache banks      //
//                                                                               //
// Revision:                                                                     //
// Revision v0.1 - File Created                                                  //
//                                                                               //
// ============================================================================= //

    `define log2(VALUE) ((VALUE) < ( 1 ) ? 0 : (VALUE) < ( 2 ) ? 1 : (VALUE) < ( 4 ) ? 2 : (VALUE)< (8) ? 3:(VALUE) < ( 16 )  ? 4 : (VALUE) < ( 32 )  ? 5 : (VALUE) < ( 64 )  ? 6 : (VALUE) < ( 128 ) ? 7 : (VALUE) < ( 256 ) ? 8 : (VALUE) < ( 512 ) ? 9 : 10)

    `define ENABLE_ICACHE 6'b00_0000
    `define FLUSH_ICACHE  6'b00_0001
    `define FLUSH_L0      6'b00_0010

    `define CLEAR_CNTS    6'b00_0011 
    `define ENABLE_CNTS   6'b00_0100


//---------- REGISTER MAP ------------//
// 0x000 --> ENABLE/DISABLE CACHE BANKS                 --> MAX 32 bit, up to 32 banks --> need register --> [NB_CACHE_BANKS-1:0]
// 0x004 --> FLUSH_ICACHE                               --> MAX 32 bit, up to 32 banks --> need register --> [NB_CACHE_BANKS-1:0]
// 0x008 --> STATUS_ICACHE (pending transactions)
// 0x00C --> FLUSH_L0_BUFFER                            --> MAX 32 bit, up to 32 banks --> need register --> [NB_CORES-1:0]

// OPTIONAL NOT WORKING ANYMORE
// 0x010 --> CLEAR_STATISTIC_COUNTERS                   --> MAX 32 bit, up to 32 banks --> need register --> [NB_CACHE_BANKS-1:0]
// 0x014 --> START_STATISTIC_COUNTERS                   --> MAX 32 bit, up to 32 banks --> need register --> [NB_CACHE_BANKS-1:0]

// 0x018 --> READ_ICACHE_HIT_CNT[Bank 0]
// 0x01C --> READ_ICACHE_HIT_CNT[Bank 1]
// 0x020 --> READ_ICACHE_HIT_CNT[Bank 2]
// 0x024 --> READ_ICACHE_HIT_CNT[Bank 3]

// 0x028 --> READ_ICACHE_TRANS_CNT[Bank 0]
// 0x02C --> READ_ICACHE_TRANS_CNT[Bank 1]
// 0x030 --> READ_ICACHE_TRANS_CNT[Bank 2]
// 0x034 --> READ_ICACHE_TRANS_CNT[Bank 3]   



//-----------------------------------//


module icache_ctrl_unit
#(
    parameter int NB_CACHE_BANKS  = 4,
    parameter int NB_CORES        = 4,
    parameter int ID_WIDTH        = 5,
    parameter bit FEATURE_STAT    = 1'b0
)
(
    input logic                                 clk_i,
    input logic                                 rst_ni,

    XBAR_PERIPH_BUS.Slave                       speriph_slave,

    ICACHE_CTRL_UNIT_BUS.Master                 IC_ctrl_unit_master_if[NB_CACHE_BANKS],
    L0_CTRL_UNIT_BUS.Master                     L0_ctrl_unit_master_if[NB_CORES]
);

    int unsigned                             i,j,k,x,y;

    localparam NUM_REGS = FEATURE_STAT ? 5 : 3;

    logic [31:0]                ICACHE_CTRL_REGS[NUM_REGS];

    // State of the main FSM
    enum logic [2:0] { IDLE, ENABLE_DISABLE_ICACHE, FLUSH_ICACHE_CHECK, FLUSH_ICACHE,
      FLUSH_L0_BUFFER, COMPLETE_FLUSH_L0_BUFFER, CLEAR_STAT_REGS, ENABLE_STAT_REGS } CS, NS;

    // Exploded Interface --> PERIPHERAL INTERFACE
    logic                req;
    logic [31:0]         addr;
    logic                wen;
    logic [31:0]         wdata;
    logic [3:0]          be;
    logic                gnt;
    logic [ID_WIDTH-1:0] id;
    logic                r_valid;
    logic                r_opc;
    logic [ID_WIDTH-1:0] r_id;
    logic [31:0]         r_rdata;


    // Internal FSM signals --> responses
    logic                                       r_valid_int;
    logic [31:0]                                r_rdata_int;

    // Exploded Interface --> CONTROL ICACHE INTERFACE
    logic [NB_CACHE_BANKS-1:0]                  req_enable;
    logic [NB_CACHE_BANKS-1:0]                  ack_enable;
    logic [NB_CACHE_BANKS-1:0]                  req_disable;
    logic [NB_CACHE_BANKS-1:0]                  ack_disable;

    //L0 Buffer Flushing signals
    logic [NB_CORES-1:0]                        flush_FetchBuffer;
    logic [NB_CORES-1:0]                        ack_flush;

    logic                                       icache_is_private;

    logic [NB_CACHE_BANKS-1:0] [31:0]           hit_count;
    logic [NB_CACHE_BANKS-1:0] [31:0]           trans_count;
    logic [NB_CACHE_BANKS-1:0]                  clear_regs;
    logic [NB_CACHE_BANKS-1:0]                  enable_regs;

    logic [NB_CACHE_BANKS-1:0]                  pending_trans;
    logic [NB_CACHE_BANKS-1:0]                  req_flush;

    logic                                       is_read;
    logic                                       is_write;
    logic                                       deliver_response;

    logic                                       listen_ack_enable;
    logic                                       clear_ack_enable;
    logic [31:0]                                sampled_ack_enable;


    logic                                       listen_ack_disable;
    logic                                       clear_ack_disable;
    logic [31:0]                                sampled_ack_disable;

    logic                                       listen_ack_flush;
    logic                                       clear_ack_flush;
    logic [31:0]                                sampled_ack_flush;

    logic [31:0]                                mask_ack_enable;
    logic [31:0]                                mask_ack_flush;

    // Interface binding
    assign speriph_slave.gnt                    = gnt;
    assign req                                  = speriph_slave.req;
    assign addr                                 = speriph_slave.add;
    assign wen                                  = speriph_slave.wen;
    assign wdata                                = speriph_slave.wdata;
    assign be                                   = speriph_slave.be;
    assign id                                   = speriph_slave.id;
    assign speriph_slave.r_valid                = r_valid;
    assign speriph_slave.r_opc                  = r_opc;
    assign speriph_slave.r_id                   = r_id;
    assign speriph_slave.r_rdata                = r_rdata;




  genvar index;

  assign flush_FetchBuffer = ICACHE_CTRL_REGS[`FLUSH_L0][NB_CORES-1:0];

  generate
        for(index = 0; index < NB_CORES; index++)
        begin
            assign L0_ctrl_unit_master_if[index].flush_FetchBuffer =  flush_FetchBuffer[index];
            assign ack_flush[index]                                =  L0_ctrl_unit_master_if[index].flush_ack;
        end

        for(index = 0; index < NB_CACHE_BANKS; index++)
        begin
            assign IC_ctrl_unit_master_if[index].ctrl_req_enable   = req_enable[index];
            assign IC_ctrl_unit_master_if[index].ctrl_req_disable  = req_disable[index];
            assign IC_ctrl_unit_master_if[index].icache_is_private = icache_is_private;
            assign ack_enable[index]                           = IC_ctrl_unit_master_if[index].ctrl_ack_enable;
            assign ack_disable[index]                          = IC_ctrl_unit_master_if[index].ctrl_ack_disable;
            assign pending_trans[index]                        = IC_ctrl_unit_master_if[index].ctrl_pending_trans;

            if (FEATURE_STAT) begin
              assign IC_ctrl_unit_master_if[index].ctrl_clear_regs  = clear_regs[index];
              assign IC_ctrl_unit_master_if[index].ctrl_enable_regs = enable_regs[index];

              assign hit_count[index]                            = IC_ctrl_unit_master_if[index].ctrl_hit_count;
              assign trans_count[index]                          = IC_ctrl_unit_master_if[index].ctrl_trans_count;
            end
        end
  endgenerate

   always_comb
   begin : REGISTER_BIND_OUT
        for(k=0; k<NB_CACHE_BANKS; k++)
        begin
            req_enable[k]  =   ICACHE_CTRL_REGS[`ENABLE_ICACHE][k];
            req_disable[k] =  ~ICACHE_CTRL_REGS[`ENABLE_ICACHE][k];
            req_flush[k]   =   ICACHE_CTRL_REGS[`FLUSH_ICACHE] [k];
            if (FEATURE_STAT) begin
              enable_regs[k] =   ICACHE_CTRL_REGS[`ENABLE_CNTS][k];
            end
        end
   end



   always_ff @(posedge clk_i, negedge rst_ni)
   begin : SEQ_PROC
      if(rst_ni == 1'b0)
      begin
              CS                  <= IDLE;
              r_id                <= '0;
              mask_ack_enable     <= '0;
              mask_ack_flush      <= '0;

              sampled_ack_enable  <= '0;
              sampled_ack_disable <= '0;
              sampled_ack_flush   <= '0;

              r_valid             <= 1'b0;
              r_rdata             <= '0;
              r_opc               <= '0;
              icache_is_private   <= 1'b0;

              for(i=0;i<NUM_REGS;i++)
                ICACHE_CTRL_REGS[i] <= '0;
      end
      else
      begin

        CS                  <= NS;

        // Track Enable icache acknow
        if(listen_ack_enable)
        begin
          for(j=0; j<NB_CACHE_BANKS; j++)
          begin
              if(ack_enable[j])
                  sampled_ack_enable[j] <= 1'b1;
          end
        end
        else
        begin
          if(clear_ack_enable)
          for(j=0; j<NB_CACHE_BANKS; j++)
          begin
                  sampled_ack_enable[j] <= 1'b0;
          end
        end


        //Track Disable Acknow
        if(listen_ack_disable)
        begin
          for(j=0; j<NB_CACHE_BANKS; j++)
          begin
              if(ack_disable[j])
                  sampled_ack_disable[j] <= 1'b1;
          end
        end
        else
        begin
          if(clear_ack_disable)
          for(j=0; j<NB_CACHE_BANKS; j++)
          begin
                  sampled_ack_disable[j] <= 1'b0;
          end
        end




        // Track FLUSH L0 Buffer acknow
        if(listen_ack_flush)
        begin
          for(j=0; j<NB_CORES; j++)
          begin
              if(ack_flush[j])
                  sampled_ack_flush[j] <= 1'b1;
          end
        end
        else
        begin
          if(clear_ack_flush)
          for(j=0; j<NB_CORES; j++)
          begin
                  sampled_ack_flush[j] <= 1'b0;
          end
        end


// handle register write
//        ICACHE_CTRL_REGS[2] <= pending_trans; //Write this register every cycle
//
// `ifdef FEATURE_ICACHE_STAT 
//         for(j=0; j<NB_CACHE_BANKS; j++)
//         begin
//             ICACHE_CTRL_REGS[6+j]                  <= hit_count[j];
//             ICACHE_CTRL_REGS[6+2*NB_CACHE_BANKS+j] <= trans_count[j];
//         end
// `endif

//---------- REGISTER MAP ------------//
// 0x000 --> ENABLE/DISABLE CACHE BANKS                 --> MAX 32 bit, up to 32 banks --> need register --> [NB_CACHE_BANKS-1:0]
// 0x004 --> FLUSH_ICACHE                               --> MAX 32 bit, up to 32 banks --> need register --> [NB_CACHE_BANKS-1:0]
// 0x008 --> STATUS_ICACHE (pending transactions)
// 0x00C --> FLUSH_L0_BUFFER                            --> MAX 32 bit, up to 32 banks --> need register --> [NB_CORES-1:0]






        if(is_write)
        begin
          case(addr[7:0])
              8'h00: // ENABLE-DISABLE
              begin
                    ICACHE_CTRL_REGS[`ENABLE_ICACHE] <= wdata;
              end

              8'h04: // FLUSH
              begin
                ICACHE_CTRL_REGS[`FLUSH_ICACHE] <= wdata;
              end

              8'h0C:
              begin
                  ICACHE_CTRL_REGS[`FLUSH_L0] <= wdata;
              end

              8'hF0:
              begin
                  icache_is_private <= wdata[0];
              end

              8'h10: // CLEAR
              if (FEATURE_STAT) begin
                ICACHE_CTRL_REGS[`CLEAR_CNTS] <= wdata;
              end

              8'h14: // ENABLE-DISABLE STAT REGS
              if (FEATURE_STAT) begin
                ICACHE_CTRL_REGS[`ENABLE_CNTS] <= wdata;
              end
          endcase
        end

        if(clear_ack_flush)
        begin
            ICACHE_CTRL_REGS[`FLUSH_L0] <= '0;
        end

        // sample the ID
        if(req & gnt)
        begin
          r_id    <= id;
          if((wen == 1'b0) && (addr[7:2] == `ENABLE_ICACHE))
              mask_ack_enable <= ~wdata;

          if((wen == 1'b0) && (addr[7:2] == `FLUSH_L0))
              mask_ack_flush <= ~wdata;
        end


        //Handle register read
        if(is_read == 1'b1)
        begin
          r_valid <= 1'b1;

          if (addr[7:2] <= 3) begin
            case(addr[7:2])
              0: r_rdata <= ICACHE_CTRL_REGS[`ENABLE_ICACHE];
              1: r_rdata <= ICACHE_CTRL_REGS[`FLUSH_ICACHE];
              2: r_rdata <= pending_trans;
              3: r_rdata <= ICACHE_CTRL_REGS[`FLUSH_L0];
            endcase
          end else if (FEATURE_STAT && addr[7:2] <= 13) begin
            case (addr[7:2])
              // Clear and start
               4: r_rdata <= ICACHE_CTRL_REGS[`CLEAR_CNTS];
               5: r_rdata <= ICACHE_CTRL_REGS[`ENABLE_CNTS];

               6: r_rdata <= hit_count[0];
               7: r_rdata <= hit_count[1];
               8: r_rdata <= hit_count[2];
               9: r_rdata <= hit_count[3];

              10: r_rdata <= trans_count[0];
              11: r_rdata <= trans_count[1];
              12: r_rdata <= trans_count[2];
              13: r_rdata <= trans_count[3];
            endcase
          end else if (addr[7:2] == 6'h3C) begin
            r_rdata <= {31'h0000_0000,icache_is_private};
          end else begin
            r_rdata <= 32'hDEAD_1C70;
          end

          r_opc   <= 1'b0;
        end
        else //no read --> IS WRITE
        begin
              if(deliver_response)
              begin
                  r_rdata <= '0;
                  r_valid <= 1'b1;
                  r_opc   <= 1'b0;
              end
              else
              begin
                  r_valid <= 1'b0;
                  r_rdata <= 'X;
                  r_opc   <= 1'b0;
              end
        end

      end
   end




   always_comb
   begin
        is_read                = 1'b0;
        is_write               = 1'b0;
        deliver_response       = 1'b0;

        listen_ack_enable      = 1'b0;
        clear_ack_enable       = 1'b0;
        listen_ack_disable     = 1'b0;
        clear_ack_disable      = 1'b0;
        listen_ack_flush       = 1'b0;
        clear_ack_flush        = 1'b0;
        gnt                    = 1'b0;
        clear_regs             = '0;

        case(CS)

          IDLE:
          begin
              gnt = 1'b1;
              clear_ack_enable       = 1'b1;
              clear_ack_disable      = 1'b1;

              if(req)
              begin
                if(wen == 1'b1) // read
                begin
                      is_read          = 1'b1;
                      NS               = IDLE;
                      deliver_response = 1'b1;
                end
                else // Write registers
                begin

                  is_write = 1'b1;
                  if (addr[7:0] <= 8'h0C) begin
                    case (addr[7:0])
                      8'h00:    NS = ENABLE_DISABLE_ICACHE;
                      8'h04:    NS = FLUSH_ICACHE_CHECK;
                      8'h0C:    NS = FLUSH_L0_BUFFER;
                      default:  NS = IDLE;
                    endcase
                  end else if (FEATURE_STAT && addr[7:0] <= 8'h14) begin
                    case (addr[7:0])
                      8'h10:    NS = CLEAR_STAT_REGS;
                      8'h14:    NS = ENABLE_STAT_REGS;
                      default:  NS = IDLE;
                    endcase
                  end else if (addr[7:0] == 8'hF0) begin
                    NS = IDLE;
                    deliver_response = 1'b1;
                  end else begin
                    NS = IDLE;
                  end

                end

              end
              else // no request
              begin
                  NS = IDLE;
              end

          end //~IDLE

          CLEAR_STAT_REGS: begin
            if (FEATURE_STAT) begin
              for(x=0; x<NB_CACHE_BANKS; x++) begin
                clear_regs[x]  =   ICACHE_CTRL_REGS[`CLEAR_CNTS][x];
              end
              deliver_response = 1'b1;
            end
            NS = IDLE;
          end //~ CLEAR_STAT_REGS


          ENABLE_STAT_REGS: begin
            if (FEATURE_STAT) begin
              deliver_response = 1'b1;
            end
            NS = IDLE;
          end

          FLUSH_L0_BUFFER : 
          begin
            gnt = 1'b0;
            listen_ack_flush       = 1'b1;

            if(   &( (sampled_ack_flush[NB_CORES-1:0] | mask_ack_flush[NB_CORES-1:0] ))   )
            begin
              NS = COMPLETE_FLUSH_L0_BUFFER;
            end
            else
            begin
              NS = FLUSH_L0_BUFFER;
            end
          end


          COMPLETE_FLUSH_L0_BUFFER :
          begin
              deliver_response = 1'b1;
              clear_ack_flush = 1'b1;
              gnt = 1'b0;
              NS = IDLE;
          end


          ENABLE_DISABLE_ICACHE: 
          begin
            gnt = 1'b0;
            listen_ack_enable      = 1'b1;
            listen_ack_disable     = 1'b1;

            if(   &( (sampled_ack_enable[NB_CACHE_BANKS-1:0] | mask_ack_enable[NB_CACHE_BANKS-1:0] )   &  (sampled_ack_disable[NB_CACHE_BANKS-1:0] | ~mask_ack_enable[NB_CACHE_BANKS-1:0] )) )
            begin
              NS = IDLE;
              deliver_response = 1'b1;
            end
            else
            begin
              NS = ENABLE_DISABLE_ICACHE;
            end
          end //~ENABLE_ICACHE



          FLUSH_ICACHE_CHECK:
          begin
              gnt = 1'b0;
              listen_ack_enable      = 1'b1;
              listen_ack_disable     = 1'b1;

              if(   &( (sampled_ack_enable[NB_CACHE_BANKS-1:0] | mask_ack_enable[NB_CACHE_BANKS-1:0] )   &  (sampled_ack_disable[NB_CACHE_BANKS-1:0] | ~mask_ack_enable[NB_CACHE_BANKS-1:0] )) )
              begin
                NS = IDLE;
                deliver_response = 1'b1;
              end
              else
              begin
                NS = FLUSH_ICACHE_CHECK;
              end
          end


        default :
        begin
                NS = IDLE;
        end
        endcase
   end


endmodule
