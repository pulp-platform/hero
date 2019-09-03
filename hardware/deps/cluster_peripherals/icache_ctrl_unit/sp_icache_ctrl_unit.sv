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

    `define ENABLE_ICACHE     6'b00_0000
    `define FLUSH_ICACHE      6'b00_0001
    `define FLUSH_L0          6'b00_0010
    `define SEL_FLUSH_ICACHE  6'b00_0011
    `define ICACHE_IS_PRI     6'b11_1111
    `define CLEAR_CNTS        6'b00_0100
    `define ENABLE_CNTS       6'b00_0101
    `define READ_ICACHE_HIT_CORES     6'b01_0000 // R Only
    `define READ_ICACHE_TRANS_CORES   6'b01_0001 // R Only
    `define READ_ICACHE_MISS_CORES    6'b01_0001 // R Only



module sp_icache_ctrl_unit
#(
    parameter int NB_CACHE_BANKS  = 4,
    parameter int NB_CORES        = 4,
    parameter int ID_WIDTH        = 5,
    parameter int OFFSET          = 4,
    parameter bit FEATURE_STAT    = 1'b0
)
(
    input logic                                 clk_i,
    input logic                                 rst_ni,

    XBAR_PERIPH_BUS.Slave                       speriph_slave,

    SP_ICACHE_CTRL_UNIT_BUS.Master              IC_ctrl_unit_master_if[NB_CACHE_BANKS],
    L0_CTRL_UNIT_BUS.Master                     L0_ctrl_unit_master_if[NB_CORES]
);

    int unsigned                             i,j,k,x,y;

    localparam NUM_REGS = FEATURE_STAT ? 6 : 3;

    logic [31:0]                ICACHE_CTRL_REGS[NUM_REGS];


    // State of the main FSM
    enum logic [3:0] { IDLE, ENABLE_DISABLE_ICACHE, FLUSH_ICACHE_CHECK, FLUSH_ICACHE,
      FLUSH_L0_BUFFER, COMPLETE_FLUSH_L0_BUFFER, SEL_FLUSH_ICACHE, CLEAR_STAT_REGS, ENABLE_STAT_REGS
    } CS, NS;


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


    // Exploded Interface --> CONTROL ICACHE INTERFACE
    logic [NB_CACHE_BANKS-1:0]                  req_enable;
    logic [NB_CACHE_BANKS-1:0]                  ack_enable;
    logic [NB_CACHE_BANKS-1:0]                  req_disable;
    logic [NB_CACHE_BANKS-1:0]                  ack_disable;
    logic [NB_CACHE_BANKS-1:0]                  req_flush_CB;
    logic [NB_CACHE_BANKS-1:0]                  ack_flush_CB;

    //L0 Buffer Flushing signals
    logic [NB_CORES-1:0]                        req_flush_FetchBuffer;
    logic [NB_CORES-1:0]                        ack_flush_FetchBuffer;

    logic                                       icache_is_private;

    logic [NB_CACHE_BANKS-1:0]                  clear_regs;   // NB_BANKS
    logic [NB_CACHE_BANKS-1:0]                  enable_regs;  // NB_BANKS

    logic [31:0]                                global_hit_count;
    logic [31:0]                                global_trans_count;
    logic [31:0]                                global_miss_count;
    logic [31:0]                                global_stall_count;

    logic [7:0][31:0]                           stall_count;       // NB_CORES 
    logic [7:0][31:0]                           bank_hit_count;    // NB_BANKS
    logic [7:0][31:0]                           bank_trans_count;  // NB_BANKS
    logic [7:0][31:0]                           bank_miss_count;   // NB_BANKS

    logic [NB_CACHE_BANKS-1:0]                  pending_trans;
    logic [NB_CACHE_BANKS-1:0]                  req_flush;

    logic                                       is_read;
    logic                                       is_write;
    logic                                       deliver_response;


    // TO CACHE CONTROLLERS
    // ----------------------------------------------------------//
    // ENABLE THE ICACHE
    logic                                       listen_ack_enable;
    logic                                       clear_ack_enable;
    logic [NB_CACHE_BANKS-1:0]                  sampled_ack_enable;
    // DISABLE THE ICACHE
    logic                                       listen_ack_disable;
    logic                                       clear_ack_disable;
    logic [NB_CACHE_BANKS-1:0]                  sampled_ack_disable;
    // FLUSH THE ICACHE
    logic                                       listen_ack_flush_CB;
    logic                                       clear_ack_flush_CB;
    logic [NB_CACHE_BANKS-1:0]                  sampled_ack_flush_CB;
    // ----------------------------------------------------------//


    // To L0 BUFFER
    // ----------------------------------------------------------//
    logic                                       listen_ack_flush_FetchBuffer;
    logic                                       clear_ack_flush_FetchBuffer;
    logic [NB_CORES-1:0]                        sampled_ack_flush_FetchBuffer;
    // ----------------------------------------------------------//



    logic [NB_CACHE_BANKS-1:0]                  mask_ack_enable;
    logic [NB_CORES-1:0]                        mask_ack_flush_FetchBuffer;
    logic [NB_CACHE_BANKS-1:0]                  mask_ack_flush_CB;


    logic [NB_CACHE_BANKS-1:0]                  sel_flush_req;
    logic [31:0]                                sel_flush_addr;
    logic [NB_CACHE_BANKS-1:0]                  sel_flush_ack;


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

  assign req_flush_FetchBuffer = ICACHE_CTRL_REGS[`FLUSH_L0][NB_CORES-1:0];


  assign sel_flush_addr  =  ICACHE_CTRL_REGS[`SEL_FLUSH_ICACHE];
  generate
        for(index = 0; index < NB_CORES; index++)
        begin
            assign L0_ctrl_unit_master_if[index].flush_FetchBuffer =  req_flush_FetchBuffer[index];
            assign ack_flush_FetchBuffer[index]                    =  L0_ctrl_unit_master_if[index].flush_ack;
            if (FEATURE_STAT) begin
              assign stall_count[index]                            =  L0_ctrl_unit_master_if[index].ctrl_stall_count;
            end
        end

        if(NB_CORES<8)
        begin
            for(index = NB_CORES; index < 8; index++)
            begin
                assign stall_count[index]  = 0;
            end
        end

        for(index = 0; index < NB_CACHE_BANKS; index++)
        begin
            assign IC_ctrl_unit_master_if[index].sel_flush_addr    = sel_flush_addr;
            assign IC_ctrl_unit_master_if[index].sel_flush_req     = sel_flush_req[index];
            assign sel_flush_ack[index]                            = IC_ctrl_unit_master_if[index].sel_flush_ack;

            assign IC_ctrl_unit_master_if[index].ctrl_req_enable   = req_enable[index];
            assign ack_enable[index]                               = IC_ctrl_unit_master_if[index].ctrl_ack_enable;
            
            assign IC_ctrl_unit_master_if[index].ctrl_req_disable  = req_disable[index];
            assign ack_disable[index]                              = IC_ctrl_unit_master_if[index].ctrl_ack_disable;
            
            assign IC_ctrl_unit_master_if[index].ctrl_flush_req    = req_flush_CB[index];
            assign ack_flush_CB[index]                             = IC_ctrl_unit_master_if[index].ctrl_flush_ack;

            assign IC_ctrl_unit_master_if[index].icache_is_private = icache_is_private;
            assign pending_trans[index]                            = IC_ctrl_unit_master_if[index].ctrl_pending_trans;


            if (FEATURE_STAT) begin
              assign IC_ctrl_unit_master_if[index].ctrl_clear_regs  = clear_regs[index];
              assign IC_ctrl_unit_master_if[index].ctrl_enable_regs = enable_regs[index];

              assign bank_hit_count[index]                          = IC_ctrl_unit_master_if[index].ctrl_hit_count;
              assign bank_trans_count[index]                        = IC_ctrl_unit_master_if[index].ctrl_trans_count;
              assign bank_miss_count[index]                         = IC_ctrl_unit_master_if[index].ctrl_miss_count;
            end
        end

        if(NB_CACHE_BANKS<8)
        begin
            for(index = NB_CACHE_BANKS; index < 8; index++)
            begin
                assign bank_hit_count[index]    = '0;
                assign bank_trans_count[index]  = '0;
                assign bank_miss_count[index]   = '0;
            end
        end
  endgenerate




   always_comb
   begin : REGISTER_BIND_OUT
        
        global_miss_count  = '0;
        global_trans_count = '0;
        global_hit_count   = '0;

        for(k=0; k<NB_CACHE_BANKS; k++)
        begin
            req_enable[k]     =   ICACHE_CTRL_REGS [`ENABLE_ICACHE] [k];
            req_disable[k]    =  ~ICACHE_CTRL_REGS [`ENABLE_ICACHE] [k];
            req_flush_CB[k]   =   ICACHE_CTRL_REGS [`FLUSH_ICACHE]  [k] &  ~(sampled_ack_flush_CB[k] | mask_ack_flush_CB[k]);

            if (FEATURE_STAT) begin
              enable_regs[k] =   ICACHE_CTRL_REGS[`ENABLE_CNTS][k];

              global_hit_count   = global_hit_count    + bank_hit_count[k];
              global_trans_count = global_trans_count  + bank_trans_count[k];
              global_miss_count  = global_miss_count   + bank_miss_count[k];
            end
        end

        global_stall_count = '0;
        if (FEATURE_STAT) begin
          for (k=0; k<NB_CACHE_BANKS; k++) begin
            global_stall_count = global_stall_count + stall_count[k];
          end
        end
   end



   always_ff @(posedge clk_i, negedge rst_ni)
   begin : SEQ_PROC
      if(rst_ni == 1'b0)
      begin
              CS                             <= IDLE;
              r_id                           <= '0;
              mask_ack_enable                <= '0;
              mask_ack_flush_FetchBuffer     <= '0;
              mask_ack_flush_CB              <= '0;

              sampled_ack_enable             <= '0;
              sampled_ack_disable            <= '0;
              sampled_ack_flush_FetchBuffer  <= '0;
              sampled_ack_flush_CB           <= '0;

              r_valid                        <= 1'b0;
              r_rdata                        <= '0;
              r_opc                          <= '0;
              icache_is_private              <= 1'b0;

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


        //Track Disable Acknow
        if(listen_ack_flush_CB)
        begin
          for(j=0; j<NB_CACHE_BANKS; j++)
          begin
              if(ack_flush_CB[j])
                  sampled_ack_flush_CB[j] <= 1'b1;
          end
        end
        else
        begin
          if(clear_ack_flush_CB)
          for(j=0; j<NB_CACHE_BANKS; j++)
          begin
                  sampled_ack_flush_CB[j] <= 1'b0;
          end
        end


        // Track FLUSH L0 Buffer acknow
        if(listen_ack_flush_FetchBuffer)
        begin
          for(j=0; j<NB_CORES; j++)
          begin
              if(ack_flush_FetchBuffer[j])
                  sampled_ack_flush_FetchBuffer[j] <= 1'b1;
          end
        end
        else
        begin
          if(clear_ack_flush_FetchBuffer)
          for(j=0; j<NB_CORES; j++)
          begin
                  sampled_ack_flush_FetchBuffer[j] <= 1'b0;
          end
        end



        if(is_write)
        begin
          casex ({addr[7:2], FEATURE_STAT})

            {`ENABLE_ICACHE, 1'bx}: begin
              ICACHE_CTRL_REGS[`ENABLE_ICACHE][NB_CACHE_BANKS-1:0]  <=  wdata[NB_CACHE_BANKS-1:0];
              mask_ack_enable                                       <= ~wdata[NB_CACHE_BANKS-1:0];
            end

            {`FLUSH_ICACHE, 1'bx}: begin
              ICACHE_CTRL_REGS[`FLUSH_ICACHE][NB_CACHE_BANKS-1:0] <=  wdata[NB_CACHE_BANKS-1:0];
              mask_ack_flush_CB                                   <= ~wdata[NB_CACHE_BANKS-1:0];
            end

            {`FLUSH_L0, 1'bx}: begin
              ICACHE_CTRL_REGS[`FLUSH_L0][NB_CACHE_BANKS-1:0] <=  wdata[NB_CORES-1:0];
              mask_ack_flush_FetchBuffer                      <= ~wdata[NB_CORES-1:0];
            end

            {`SEL_FLUSH_ICACHE, 1'bx}: begin
              // The regs store the address
              ICACHE_CTRL_REGS[`SEL_FLUSH_ICACHE] <= wdata;
            end

            {`ICACHE_IS_PRI, 1'bx}: begin
              icache_is_private <= wdata[0];
            end

            {`CLEAR_CNTS, 1'b1}: begin
              ICACHE_CTRL_REGS[`CLEAR_CNTS] <= wdata;
            end

            {`ENABLE_CNTS, 1'b1}: begin
              ICACHE_CTRL_REGS[`ENABLE_CNTS] <= wdata;
            end

          endcase
        end
        else
        begin
                // reset status bits for FLUSH
                if(clear_ack_flush_FetchBuffer)
                begin
                    ICACHE_CTRL_REGS[`FLUSH_L0] <= '0;
                end

                if(clear_ack_flush_CB)
                begin
                    ICACHE_CTRL_REGS[`FLUSH_ICACHE] <= '0;
                end
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
            {`ENABLE_ICACHE,    1'bx}:  r_rdata <= ICACHE_CTRL_REGS[`ENABLE_ICACHE];
            {`FLUSH_ICACHE,     1'bx}:  r_rdata <= ICACHE_CTRL_REGS[`FLUSH_ICACHE];
            {`FLUSH_L0,         1'bx}:  r_rdata <= ICACHE_CTRL_REGS[`FLUSH_L0];
            {`SEL_FLUSH_ICACHE, 1'bx}:  r_rdata <= ICACHE_CTRL_REGS[`SEL_FLUSH_ICACHE];
            {`ICACHE_IS_PRI,    1'bx}:  r_rdata <= {31'h0000_0000,icache_is_private};

            {`CLEAR_CNTS,       1'b1}:  r_rdata <= ICACHE_CTRL_REGS[`CLEAR_CNTS];
            {`ENABLE_CNTS,      1'b1}:  r_rdata <= ICACHE_CTRL_REGS[`ENABLE_CNTS];

            {6'd08,             1'b1}:  r_rdata <= global_hit_count;
            {6'd09,             1'b1}:  r_rdata <= global_trans_count;
            {6'd10,             1'b1}:  r_rdata <= global_miss_count;
            {6'd11,             1'b1}:  r_rdata <= global_stall_count;

            {6'd12,             1'b1}:  r_rdata <= bank_hit_count  [0];
            {6'd13,             1'b1}:  r_rdata <= bank_trans_count[0];
            {6'd14,             1'b1}:  r_rdata <= bank_miss_count [0];

            {6'd15,             1'b1}:  r_rdata <= bank_hit_count  [1];
            {6'd16,             1'b1}:  r_rdata <= bank_trans_count[1];
            {6'd17,             1'b1}:  r_rdata <= bank_miss_count [1];

            {6'd18,             1'b1}:  r_rdata <= bank_hit_count  [2];
            {6'd19,             1'b1}:  r_rdata <= bank_trans_count[2];
            {6'd20,             1'b1}:  r_rdata <= bank_miss_count [2];

            {6'd21,             1'b1}:  r_rdata <= bank_hit_count  [3];
            {6'd22,             1'b1}:  r_rdata <= bank_trans_count[3];
            {6'd23,             1'b1}:  r_rdata <= bank_miss_count [3];

            {6'd24,             1'b1}:  r_rdata <= bank_hit_count  [4];
            {6'd25,             1'b1}:  r_rdata <= bank_trans_count[4];
            {6'd26,             1'b1}:  r_rdata <= bank_miss_count [4];

            {6'd27,             1'b1}:  r_rdata <= bank_hit_count  [5];
            {6'd28,             1'b1}:  r_rdata <= bank_trans_count[5];
            {6'd29,             1'b1}:  r_rdata <= bank_miss_count [5];

            {6'd30,             1'b1}:  r_rdata <= bank_hit_count  [6];
            {6'd31,             1'b1}:  r_rdata <= bank_trans_count[6];
            {6'd32,             1'b1}:  r_rdata <= bank_miss_count [6];

            {6'd33,             1'b1}:  r_rdata <= bank_hit_count  [7];
            {6'd34,             1'b1}:  r_rdata <= bank_trans_count[7];
            {6'd35,             1'b1}:  r_rdata <= bank_miss_count [7];

            {6'd36,             1'b1}:  r_rdata <= stall_count[0];
            {6'd37,             1'b1}:  r_rdata <= stall_count[1];
            {6'd38,             1'b1}:  r_rdata <= stall_count[2];
            {6'd39,             1'b1}:  r_rdata <= stall_count[3];
            {6'd40,             1'b1}:  r_rdata <= stall_count[4];
            {6'd41,             1'b1}:  r_rdata <= stall_count[5];
            {6'd42,             1'b1}:  r_rdata <= stall_count[6];
            {6'd43,             1'b1}:  r_rdata <= stall_count[7];

            default:                    r_rdata <= 32'hBADACCE5;
          endcase
          r_opc   <= 1'b0;
        end
        else //no read --> IS WRITE
        begin
              if(deliver_response)
              begin
                  r_valid <= 1'b1;
                  r_opc   <= 1'b0;
                  r_rdata <= '0; //
              end
              else
              begin
                  r_valid <= 1'b0;
                  r_opc   <= 1'b0;
              end
        end

      end
   end




   always_comb
   begin
        gnt                    = 1'b0;
        
        is_read                = 1'b0;
        is_write               = 1'b0;
        deliver_response       = 1'b0;

        listen_ack_enable      = 1'b0;
        clear_ack_enable       = 1'b0;
        
        listen_ack_disable     = 1'b0;
        clear_ack_disable      = 1'b0;

        sel_flush_req          = '0;


        listen_ack_flush_FetchBuffer = 1'b0;
        clear_ack_flush_FetchBuffer  = 1'b0;

        listen_ack_flush_CB      = 1'b0;
        clear_ack_flush_CB       = 1'b0;        
        
        clear_regs             = '0;

        case(CS)

          IDLE:
          begin
              gnt                          = 1'b1;
              clear_ack_enable             = 1'b1;
              clear_ack_disable            = 1'b1;
              clear_ack_flush_CB           = 1'b1;
              clear_ack_flush_FetchBuffer  = 1'b1;

              if(req)
              begin
                if(wen) // read
                begin
                      is_read          = 1'b1;
                      NS               = IDLE;
                      deliver_response = 1'b1;
                end
                else // Write registers
                begin
                  is_write = 1'b1;
                  casex ({addr[7:2], FEATURE_STAT})
                    {`ENABLE_ICACHE,    1'bx}:  NS = ENABLE_DISABLE_ICACHE;
                    {`FLUSH_ICACHE,     1'bx}:  NS = FLUSH_ICACHE_CHECK;
                    {`FLUSH_L0,         1'bx}:  NS = FLUSH_L0_BUFFER;
                    {`SEL_FLUSH_ICACHE, 1'bx}:  NS = SEL_FLUSH_ICACHE;

                    {`CLEAR_CNTS,       1'b1}:  NS = CLEAR_STAT_REGS;
                    {`ENABLE_CNTS,      1'b1}:  NS = ENABLE_STAT_REGS;

                    {`ICACHE_IS_PRI,    1'bx}: begin
                      NS = IDLE;
                      deliver_response = 1'b1;
                    end

                    default:                    NS = IDLE;
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
              for (x=0; x<NB_CACHE_BANKS; x++) begin
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

          // L0 BUFFER FLUSHING STATES
          FLUSH_L0_BUFFER : 
          begin
            gnt                           = 1'b0;
            listen_ack_flush_FetchBuffer  = 1'b1;

            if(   &( (sampled_ack_flush_FetchBuffer[NB_CORES-1:0] | mask_ack_flush_FetchBuffer[NB_CORES-1:0] ))   )
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
              deliver_response            = 1'b1;
              clear_ack_flush_FetchBuffer = 1'b1;
              gnt                         = 1'b0;
              NS                          = IDLE;
          end







          ENABLE_DISABLE_ICACHE: 
          begin
            gnt                    = 1'b0;
            listen_ack_enable      = 1'b1;
            listen_ack_disable     = 1'b1;

            if(   &( (sampled_ack_enable[NB_CACHE_BANKS-1:0] | mask_ack_enable[NB_CACHE_BANKS-1:0] )   &  (sampled_ack_disable[NB_CACHE_BANKS-1:0] | ~mask_ack_enable[NB_CACHE_BANKS-1:0] )) )
            begin
              NS               = IDLE;
              deliver_response = 1'b1;
            end
            else
            begin
              NS = ENABLE_DISABLE_ICACHE;
            end
          end //~ENABLE_ICACHE



          FLUSH_ICACHE_CHECK:
          begin
              gnt                       = 1'b0;
              listen_ack_flush_CB       = 1'b1;

              if(   &( sampled_ack_flush_CB[NB_CACHE_BANKS-1:0] | mask_ack_flush_CB[NB_CACHE_BANKS-1:0]  ) )
              begin
                NS = IDLE;
                deliver_response = 1'b1;
              end
              else
              begin
                NS = FLUSH_ICACHE_CHECK;
              end
          end



          SEL_FLUSH_ICACHE:
          begin
              sel_flush_req = '0;
              sel_flush_req[sel_flush_addr[ $clog2(NB_CACHE_BANKS)-1+OFFSET:OFFSET]] = 1'b1;
              
              if( sel_flush_ack[sel_flush_addr[$clog2(NB_CACHE_BANKS)-1+OFFSET:OFFSET ]])
              begin
                NS = IDLE;
                deliver_response = 1'b1;
              end
              else
              begin
                NS = SEL_FLUSH_ICACHE;
              end
          end


        default :
        begin
                NS = IDLE;
        end
        endcase
   end


endmodule
