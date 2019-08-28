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

    `define ENABLE_ICACHE 6'b00_0000
    `define FLUSH_ICACHE  6'b00_0001
    `define CLEAR_CNTS    6'b00_0011 
    `define ENABLE_CNTS   6'b00_0100


//-----------------------------------//


module pri_icache_ctrl_unit
#(
    parameter int NB_CACHE_BANKS  = 8,
    parameter int NB_CORES        = 8,
    parameter int ID_WIDTH        = 5,
    parameter bit FEATURE_STAT    = 1'b0
)
(
    input logic                                 clk_i,
    input logic                                 rst_ni,

    XBAR_PERIPH_BUS.Slave                       speriph_slave,
    PRI_ICACHE_CTRL_UNIT_BUS.Master             IC_ctrl_unit_master_if[NB_CORES]
);

   int unsigned                             i,j,k,x,y;
   genvar index;


    localparam NUM_REGS = FEATURE_STAT ? 6 : 2;

    logic [NB_CORES-1:0]                 icache_bypass_req_o;
    logic [NB_CORES-1:0]                 icache_bypass_ack_i;

    logic [NB_CORES-1:0]                 icache_flush_req_o;
    logic [NB_CORES-1:0]                 icache_flush_ack_i;

    logic [31:0]                ICACHE_CTRL_REGS[NUM_REGS];

    // State of the main FSM
    enum logic [2:0] { IDLE, ENABLE_ICACHE, DISABLE_ICACHE, FLUSH_ICACHE_CHECK, CLEAR_STAT_REGS,
      ENABLE_STAT_REGS } CS, NS;

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

    logic [7:0] [31:0]                          hit_count;
    logic [7:0] [31:0]                          trans_count;
    logic [7:0] [31:0]                          miss_count;
    logic [NB_CORES-1:0]                        clear_regs;
    logic [NB_CORES-1:0]                        enable_regs;

    logic [31:0]                                global_hit_count;
    logic [31:0]                                global_trans_count;
    logic [31:0]                                global_miss_count;

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








generate
  for(index=0;index<NB_CORES;index++)
  begin
        assign IC_ctrl_unit_master_if[index].bypass_req         = icache_bypass_req_o[index];
        assign icache_bypass_ack_i[index]                       = IC_ctrl_unit_master_if[index].bypass_ack;
        assign IC_ctrl_unit_master_if[index].flush_req          = icache_flush_req_o[index];
        assign icache_flush_ack_i[index]                        = IC_ctrl_unit_master_if[index].flush_ack;

        if (FEATURE_STAT) begin
          assign IC_ctrl_unit_master_if[index].ctrl_clear_regs    = clear_regs[index];
          assign IC_ctrl_unit_master_if[index].ctrl_enable_regs   = enable_regs[index];
        end
  end


  for(index=0;index<8;index++)
  begin
      if(index < NB_CORES )
      begin
        assign hit_count[index]                           = IC_ctrl_unit_master_if[index].ctrl_hit_count;
        assign trans_count[index]                         = IC_ctrl_unit_master_if[index].ctrl_trans_count; 
        assign miss_count[index]                          = IC_ctrl_unit_master_if[index].ctrl_miss_count; 
      end
      else
      begin
        assign hit_count[index]                           = 32'hDEAD_A555;
        assign trans_count[index]                         = 32'hDEAD_A555; 
        assign miss_count[index]                          = 32'hDEAD_A555;
      end


  end
endgenerate

 
   always_comb
   begin : REGISTER_BIND_OUT
      icache_bypass_req_o  =  ~ICACHE_CTRL_REGS[`ENABLE_ICACHE][NB_CORES-1:0];
      icache_flush_req_o   =   ICACHE_CTRL_REGS[`FLUSH_ICACHE][NB_CORES-1:0];
      if (FEATURE_STAT) begin
        enable_regs = ICACHE_CTRL_REGS[`ENABLE_CNTS][NB_CORES-1:0];
      end
   end

  if (FEATURE_STAT) begin
    always_comb
    begin
      global_hit_count   = '0;
      global_trans_count = '0;
      global_miss_count  = '0;

      for(i=0; i<NB_CORES; i++)
      begin
         global_hit_count   = global_hit_count   + hit_count[i];
         global_trans_count = global_trans_count + trans_count[i];
         global_miss_count  = global_miss_count  + miss_count[i];
      end
    end
  end

   always_ff @(posedge clk_i, negedge rst_ni)
   begin : SEQ_PROC
      if(rst_ni == 1'b0)
      begin
         CS                  <= IDLE;
         r_id                <= '0;

         r_valid             <= 1'b0;
         r_rdata             <= '0;
         r_opc               <= '0;

         sampled_ack_enable  <= '0;
         sampled_ack_disable <= '0;

         for(j=0;j<NUM_REGS;j++)
            ICACHE_CTRL_REGS[j] <= '0;
      end
      else
      begin

        CS                  <= NS;




        // Track Enable icache acknow
        if(listen_ack_enable)
        begin
          for(j=0; j<NB_CORES; j++)
          begin
              if(icache_bypass_ack_i[j] == 1'b0)
                  sampled_ack_enable[j] <= 1'b1;
          end
        end
        else
        begin
          if(clear_ack_enable)
          for(j=0; j<NB_CORES; j++)
          begin
                  sampled_ack_enable[j] <= 1'b0;
          end
        end



        // Track Enable icache acknow
        if(listen_ack_disable)
        begin
          for(j=0; j<NB_CORES; j++)
          begin
              if(icache_bypass_ack_i[j] == 1'b1)
                  sampled_ack_disable[j] <= 1'b1;
          end
        end
        else
        begin
          if(clear_ack_disable)
          for(j=0; j<NB_CORES; j++)
          begin
                  sampled_ack_disable[j] <= 1'b0;
          end
        end







        // Track Flush icache acknow
        if(listen_ack_flush)
        begin
          for(j=0; j<NB_CORES; j++)
          begin
              if(icache_flush_ack_i[j])
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



        if(is_write)
        begin
          casex ({addr[7:0], FEATURE_STAT})
            {8'h00, 1'bx}: ICACHE_CTRL_REGS[`ENABLE_ICACHE] <= wdata;
            {8'h04, 1'bx}: ICACHE_CTRL_REGS[`FLUSH_ICACHE]  <= wdata;
            {8'h0C, 1'b1}: ICACHE_CTRL_REGS[`CLEAR_CNTS]    <= wdata;
            {8'h10, 1'b1}: ICACHE_CTRL_REGS[`ENABLE_CNTS]   <= wdata;
          endcase
        end

        // sample the ID
        if(req & gnt)
        begin
          r_id    <= id;
        end


        //Handle register read
        if (is_read) begin
          r_valid <= 1'b1;
          casex ({addr[7:2], FEATURE_STAT})
            {6'd00, 1'bx}:  r_rdata <= ICACHE_CTRL_REGS[`ENABLE_ICACHE];
            {6'd01, 1'bx}:  r_rdata <= ICACHE_CTRL_REGS[`FLUSH_ICACHE];
            {6'd02, 1'bx}:  r_rdata <= 32'hBADD_A555;

            {6'd03, 1'b1}:  r_rdata <= ICACHE_CTRL_REGS[`CLEAR_CNTS];
            {6'd04, 1'b1}:  r_rdata <= ICACHE_CTRL_REGS[`ENABLE_CNTS];

            {6'd05, 1'b1}:  r_rdata <= global_hit_count;
            {6'd06, 1'b1}:  r_rdata <= global_trans_count;
            {6'd07, 1'b1}:  r_rdata <= global_miss_count;
            {6'd08, 1'b1}:  r_rdata <= 32'hFFFF_FFFF;

            {6'd09, 1'b1}:  r_rdata <= hit_count  [0];
            {6'd10, 1'b1}:  r_rdata <= trans_count[0];
            {6'd11, 1'b1}:  r_rdata <= miss_count [0];

            {6'd12, 1'b1}:  r_rdata <= hit_count  [1];
            {6'd13, 1'b1}:  r_rdata <= trans_count[1];
            {6'd14, 1'b1}:  r_rdata <= miss_count [1];

            {6'd15, 1'b1}:  r_rdata <= hit_count  [2];
            {6'd16, 1'b1}:  r_rdata <= trans_count[2];
            {6'd17, 1'b1}:  r_rdata <= miss_count [2];

            {6'd18, 1'b1}:  r_rdata <= hit_count  [3];
            {6'd19, 1'b1}:  r_rdata <= trans_count[3];
            {6'd20, 1'b1}:  r_rdata <= miss_count [3];

            {6'd21, 1'b1}:  r_rdata <= hit_count  [4];
            {6'd22, 1'b1}:  r_rdata <= trans_count[4];
            {6'd23, 1'b1}:  r_rdata <= miss_count [4];

            {6'd24, 1'b1}:  r_rdata <= hit_count  [5];
            {6'd25, 1'b1}:  r_rdata <= trans_count[5];
            {6'd26, 1'b1}:  r_rdata <= miss_count [5];

            {6'd27, 1'b1}:  r_rdata <= hit_count  [6];
            {6'd28, 1'b1}:  r_rdata <= trans_count[6];
            {6'd29, 1'b1}:  r_rdata <= miss_count [6];

            {6'd30, 1'b1}:  r_rdata <= hit_count  [7];
            {6'd31, 1'b1}:  r_rdata <= trans_count[7];
            {6'd32, 1'b1}:  r_rdata <= miss_count [7];

            {6'd33, 1'b1},
            {6'd34, 1'b1},
            {6'd35, 1'b1},
            {6'd36, 1'b1},
            {6'd37, 1'b1},
            {6'd38, 1'b1},
            {6'd39, 1'b1},
            {6'd40, 1'b1}:  r_rdata <= 32'hFFFF_FFFF;

            default:        r_rdata <= 32'hDEAD_A555;
          endcase
          r_opc <= 1'b0;

        end else begin
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
        gnt                    = 1'b0;

        listen_ack_enable      = 1'b0;
        listen_ack_disable     = 1'b0;
        listen_ack_flush       = 1'b0;

        clear_ack_flush        = 1'b0;
        clear_ack_enable       = 1'b0;
        clear_ack_disable      = 1'b0;

        clear_regs             = '0;

        case(CS)

          IDLE:
          begin
              gnt = 1'b1;

              if(req)
              begin
                if(wen == 1'b1) // read
                begin
                      is_read          = 1'b1;
                      NS               = IDLE;
                      deliver_response = 1'b1;
                end else begin // Write registers
                  is_write = 1'b1;
                  casex ({addr[7:2], FEATURE_STAT})
                    {`ENABLE_ICACHE,  1'bx}:  NS = (wdata == 0) ? DISABLE_ICACHE : ENABLE_ICACHE;
                    {`FLUSH_ICACHE,   1'bx}:  NS = FLUSH_ICACHE_CHECK;
                    {`CLEAR_CNTS,     1'b1}:  NS = CLEAR_STAT_REGS;
                    {`ENABLE_CNTS,    1'b1}:  NS = ENABLE_STAT_REGS;
                    default:                  NS = IDLE;
                  endcase
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
          end //~ENABLE_STAT_REGS

          ENABLE_ICACHE: 
          begin
            gnt                    = 1'b0;
            listen_ack_enable      = 1'b1;
            
            if( &(sampled_ack_enable[NB_CORES-1:0]) )
            begin
              NS = IDLE;
              deliver_response = 1'b1;
              clear_ack_enable = 1'b1;
            end
            else
            begin
              NS = ENABLE_ICACHE;
            end
          end //~ENABLE_ICACHE


          DISABLE_ICACHE: 
          begin
            gnt                    = 1'b0;
            listen_ack_disable     = 1'b1;

            if( &(sampled_ack_disable[NB_CORES-1:0]) )
            begin
              NS = IDLE;
              deliver_response = 1'b1;
              clear_ack_disable = 1'b1;
            end
            else
            begin
              NS = DISABLE_ICACHE;
            end
          end //~DISABLE_ICACHE




          FLUSH_ICACHE_CHECK:
          begin
              gnt = 1'b0;

              if(&sampled_ack_flush[NB_CORES-1:0])
              begin
                NS = IDLE;
                deliver_response = 1'b1;
                clear_ack_flush  = 1'b1;
              end
              else
              begin
                NS = FLUSH_ICACHE_CHECK;
                listen_ack_flush = 1'b1;
              end
          end


        default :
        begin
                NS = IDLE;
        end
        endcase
   end


endmodule
