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

    `define ENABLE_ICACHE     6'b00_0000 // W only --> Enable or Disable icache (use wdata[0])
    `define FLUSH_ICACHE      6'b00_0001 // W only --> Full FLUSH icache 
    `define SEL_FLUSH_ICACHE  6'b00_0010 // W Only --> Selective FLush (use wdata for address)
    `define ICACHE_STATUS     6'b00_0011 // R Only --> Check if the cache is bypassed (0) oe enabled (1)


    `define CLEAR_CNTS                6'b00_0100 // W Only
    `define ENABLE_CNTS               6'b00_0101 // W and R

    `define READ_ICACHE_HIT_CORES     6'b01_0000 // R Only
    `define READ_ICACHE_TRANS_CORES   6'b01_0001 // R Only

//---------- REGISTER MAP ------------//
// 0x000 --> ENABLE/DISABLE CACHE BANKS                  // W Only
// 0x004 --> FLUSH_ICACHE                                // W Only
// 0x008 --> SELECTIVE FLUSH_ICACHE                      // W Only
// 0x00C --> CHECK ICACHE STATUS (1=Disabled, 0=Enabled) // R Only                  
                                         
// PERF COUNTERS          
// 0x010 --> CLEAR_STATISTIC_COUNTERS                     // W Only
// 0x014 --> START_STATISTIC_COUNTERS (1 start, 0 Stop)   // RW
// 0x040 --> READ_ICACHE_TOTAL_HIT                        // R Only
// 0x044 --> READ_ICACHE_TOTAL_TRANS                      // R Only
//-----------------------------------//


module new_icache_ctrl_unit
#(
    parameter int NB_CACHE_BANKS  = 8,
    parameter int NB_CORES        = 8,
    parameter int ID_WIDTH        = 9,
    parameter bit FEATURE_STAT    = 1'b0
)
(
   input logic                                 clk_i,
   input logic                                 rst_ni,

   XBAR_PERIPH_BUS.Slave                       speriph_slave,
   NEW_ICACHE_CTRL_UNIT_BUS.Master             IC_ctrl_unit_master_if
);
 
   logic                                icache_status, icache_status_next;
   logic                                icache_bypass_req_o, icache_bypass_req_next;
   logic [NB_CORES:0]                   icache_bypass_ack_i;

   logic                                icache_flush_req_o, icache_flush_req_next;
   logic                                icache_flush_ack_i;

   logic                                icache_sel_flush_req_o, icache_sel_flush_req_next;
   logic [31:0]                         icache_sel_flush_addr_o;
   logic                                icache_sel_flush_ack_i;

    // State of the main FSM
    enum logic [2:0] { IDLE, ENABLE_ICACHE,  DISABLE_ICACHE, FLUSH_ICACHE, SEL_FLUSH_ICACHE,
      CLEAR_STAT_REGS, ENABLE_STAT_REGS } CS, NS;

    // Exploded Interface --> PERIPHERAL INTERFACE
    logic                         req;
    logic [31:0]                  addr;
    logic                         wen;
    logic [31:0]                  wdata;
    logic [3:0]                   be;
    logic                         gnt;
    logic [ID_WIDTH-1:0]          id;
    logic                         r_valid;
    logic                         r_opc;
    logic [ID_WIDTH-1:0]          r_id;
    logic [31:0]                  r_rdata;

    logic [31:0]                  hit_count;
    logic [31:0]                  trans_count;
    logic                         clear_regs;
    logic                         enable_regs, enable_regs_next;

    logic                         is_read;
    logic                         is_write;
    logic                         deliver_response;

    assign is_read   = (req & gnt &  wen);
    assign is_write  = (req & gnt & ~wen);

    // Interface binding
    assign speriph_slave.gnt       = gnt;
    assign req                     = speriph_slave.req;
    assign addr                    = speriph_slave.add;
    assign wen                     = speriph_slave.wen;
    assign wdata                   = speriph_slave.wdata;
    assign be                      = speriph_slave.be;
    assign id                      = speriph_slave.id;
    assign speriph_slave.r_valid   = r_valid;
    assign speriph_slave.r_opc     = r_opc;
    assign speriph_slave.r_id      = r_id;
    assign speriph_slave.r_rdata   = r_rdata;


   

    assign IC_ctrl_unit_master_if.bypass_req       = icache_bypass_req_o;
    assign icache_bypass_ack_i                     = IC_ctrl_unit_master_if.bypass_ack;
    assign IC_ctrl_unit_master_if.flush_req        = icache_flush_req_o;
    assign icache_flush_ack_i                      = IC_ctrl_unit_master_if.flush_ack;
    
    assign IC_ctrl_unit_master_if.sel_flush_req    = icache_sel_flush_req_o;
    assign IC_ctrl_unit_master_if.sel_flush_addr   = icache_sel_flush_addr_o;
    assign icache_sel_flush_ack_i                  = IC_ctrl_unit_master_if.sel_flush_ack;

    if (FEATURE_STAT) begin
      assign IC_ctrl_unit_master_if.ctrl_clear_regs  = clear_regs;
      assign IC_ctrl_unit_master_if.ctrl_enable_regs = enable_regs;

      assign hit_count                               = IC_ctrl_unit_master_if.ctrl_hit_count;
      assign trans_count                             = IC_ctrl_unit_master_if.ctrl_trans_count;
    end


always_ff @(posedge clk_i or negedge rst_ni) 
begin
   if(~rst_ni)
   begin
      icache_bypass_req_o     <= '1;
      icache_flush_req_o      <= '0;
      icache_sel_flush_req_o  <= '0;
      icache_sel_flush_addr_o <= '0;
      if (FEATURE_STAT) begin
        enable_regs           <= '0;
      end
      icache_status           <= '0;

      CS                      <= IDLE;
      r_id                    <= '0;
      r_valid                 <= 1'b0;
      r_rdata                 <= '0;
      r_opc                   <= '0;
   end 
   else // NOT RESET
   begin
         CS <= NS;

         icache_bypass_req_o     <= icache_bypass_req_next;
         icache_flush_req_o      <= icache_flush_req_next;
         icache_sel_flush_req_o  <= icache_sel_flush_req_next;
         icache_status           <= icache_status_next;
         
         if((is_write == 1'b1) && ( addr[7:2] == 6'h02))
            icache_sel_flush_addr_o <= wdata;

         if (FEATURE_STAT) begin
           enable_regs <= enable_regs_next;
         end

         // sample the ID
         if(req & gnt)
         begin
          r_id  <= id;
         end

         if(deliver_response)
         begin
            r_valid <= 1'b1;
            r_opc   <= 1'b0;
            casex ({addr[7:2], FEATURE_STAT})
              {6'h03, 1'bx}: begin
                r_rdata[31:1] <= '0;
                r_rdata[0]    <= icache_status;
              end
              {6'h05, 1'b1}: begin
                r_rdata[31:1] <= '0;
                r_rdata[0]    <= enable_regs;
              end
              {6'h10, 1'b1}: begin
                r_rdata       <= hit_count;
              end
              {6'h11, 1'b1}: begin
                r_rdata       <= trans_count;
              end
              default: begin
                r_rdata       <= 32'hBADD_A555;
              end
            endcase
         end
         else
         begin
            r_valid <= 1'b0;
            r_rdata <= 'X;
            r_opc   <= 1'b0;
         end

   end // End of if(Reset)
end // end of always_ff






always_comb
begin
   //default;
   icache_status_next         =  icache_status;
   deliver_response           =  1'b0;
   gnt                        =  1'b0;
   icache_bypass_req_next     =  icache_bypass_req_o;
   icache_flush_req_next      =  icache_flush_req_o;
   icache_sel_flush_req_next  =  1'b0;

   clear_regs                 = '0;
   enable_regs_next           =  enable_regs;

   case(CS)

      IDLE:
      begin
        gnt = 1'b1;
        if (is_read) begin
          NS               = IDLE;
          deliver_response = 1'b1;
        end else if (is_write) begin
          casex ({addr[7:2], FEATURE_STAT})

            {6'h00, 1'bx}: begin
              if (wdata[0]) begin
                NS = ENABLE_ICACHE;
                icache_bypass_req_next = 1'b0;
              end else begin
                NS = DISABLE_ICACHE;
                icache_bypass_req_next = 1'b1;
              end
            end

            {6'h01, 1'bx}: begin
              NS = FLUSH_ICACHE;
              icache_flush_req_next = 1'b1;
            end

            {6'h02, 1'bx}: begin
              NS = SEL_FLUSH_ICACHE;
              icache_sel_flush_req_next = 1'b1;
            end

            {6'h04, 1'b1}: begin // CLEAR
              NS = IDLE;
              clear_regs = 1'b1;
              deliver_response = 1'b1;
            end

            {6'h05, 1'b1}: begin // START
              NS = IDLE;
              enable_regs_next = wdata[0];
              deliver_response = 1'b1;
            end

            default: begin
              NS = IDLE;
            end
          endcase
        end else begin
          NS = IDLE;
        end
      end

      ENABLE_ICACHE: 
      begin
         gnt = 1'b0;
         if(|icache_bypass_ack_i == 1'b0) //11111 --> all bypassed; 00000 --> all enabled
         begin
            NS = IDLE;
            icache_status_next = 1'b1;
            deliver_response   = 1'b1;
         end
         else
         begin
            NS = ENABLE_ICACHE;
         end
      end //~ENABLE_ICACHE

      DISABLE_ICACHE: 
      begin
         gnt = 1'b0;

         if(&icache_bypass_ack_i == 1'b1) //11111 --> all bypassed; 00000 --> all enabled
         begin
            NS = IDLE;
            deliver_response   = 1'b1;
            icache_status_next = 1'b0;
         end
         else
         begin
            NS = DISABLE_ICACHE;
         end
      end //~DIABLE_ICACHE

      FLUSH_ICACHE:
      begin
         gnt = 1'b0;

         if(icache_flush_ack_i)
         begin
            NS = IDLE;
            deliver_response = 1'b1;
            icache_flush_req_next = 1'b0;
         end
         else
         begin
            NS = FLUSH_ICACHE;
         end
      end

      SEL_FLUSH_ICACHE:
      begin
         gnt = 1'b0;
         icache_sel_flush_req_next = 1'b1;

         if(icache_flush_ack_i)
         begin
            NS = IDLE;
            deliver_response = 1'b1;
         end
         else
         begin
            NS = FLUSH_ICACHE;
         end
      end

      default:
      begin
         NS = IDLE;
      end

   endcase // CS
end


endmodule
