// ========================================================================== //
//                           COPYRIGHT NOTICE                                 //
// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
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
//                                                                               //
// Additional contributions by:                                                  //
//                                                                               //
//                                                                               //
//                                                                               //
// Create Date:    18/08/2014                                                    //
// Design Name:    icache_ctrl_unit                                              //
// Module Name:    icache_ctrl_unit                                              //
// Project Name:   ULPSoC                                                        //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:    ICACHE control Unit, used to enable/disable icache banks      //
//                 flush operations, and to debug the status og cache banks      //
//                                                                               //
// Revision:                                                                     //
// Revision v0.1 - File Created                                                  //
//                                                                               //
//                                                                               //
//                                                                               //
//                                                                               //
//                                                                               //
//                                                                               //
// ============================================================================= //

`define FEATURE_ICACHE_STAT

    `define ENABLE_ICACHE             6'b00_0000 //0x00
    `define FLUSH_ICACHE              6'b00_0001 //0x04
    `define FLUSH_L1_ONLY             6'b00_0010 //0x08
    `define SEL_FLUSH_ICACHE          6'b00_0011 //0x0C

`ifdef FEATURE_ICACHE_STAT  //TO BE TESTED DEEPLY
    `define CLEAR_CNTS                6'b00_0100 //0x10
    `define ENABLE_CNTS               6'b00_0101 //0x14
`endif
    `define ENABLE_BYPASS             6'b00_0110 //0x18
    `define ENABLE_L1_L15_PREFETCH    6'b00_0111 //0x1C


//-----------------------------------//


module hier_icache_ctrl_unit
#(
    parameter  NB_CACHE_BANKS = 4,
    parameter  NB_CORES       = 9,
    parameter  ID_WIDTH       = 5
)
(
    input logic                                 clk_i,
    input logic                                 rst_ni,

    // Exploded Interface --> PERIPHERAL INTERFACE
    input  logic                                 speriph_slave_req_i,
    input  logic [31:0]                          speriph_slave_addr_i,
    input  logic                                 speriph_slave_wen_i,
    input  logic [31:0]                          speriph_slave_wdata_i,
    input  logic [3:0]                           speriph_slave_be_i,
    output logic                                 speriph_slave_gnt_o,
    input  logic [ID_WIDTH-1:0]                  speriph_slave_id_i,
    output logic                                 speriph_slave_r_valid_o,
    output logic                                 speriph_slave_r_opc_o,
    output logic [ID_WIDTH-1:0]                  speriph_slave_r_id_o,
    output logic [31:0]                          speriph_slave_r_rdata_o,


    output logic [NB_CORES-1:0]                  L1_icache_bypass_req_o,
    input  logic [NB_CORES-1:0]                  L1_icache_bypass_ack_i,
    output logic [NB_CORES-1:0]                  L1_icache_flush_req_o,
    input  logic [NB_CORES-1:0]                  L1_icache_flush_ack_i,
    output logic [NB_CORES-1:0]                  L1_icache_sel_flush_req_o,
    output logic [31:0]                          L1_icache_sel_flush_addr_o,
    input  logic [NB_CORES-1:0]                  L1_icache_sel_flush_ack_i,


    output logic [NB_CACHE_BANKS-1:0]            L2_icache_enable_req_o,
    input  logic [NB_CACHE_BANKS-1:0]            L2_icache_enable_ack_i,
    output logic [NB_CACHE_BANKS-1:0]            L2_icache_disable_req_o,
    input  logic [NB_CACHE_BANKS-1:0]            L2_icache_disable_ack_i,
    output logic [NB_CACHE_BANKS-1:0]            L2_icache_flush_req_o,
    input  logic [NB_CACHE_BANKS-1:0]            L2_icache_flush_ack_i,
    output logic [NB_CACHE_BANKS-1:0]            L2_icache_sel_flush_req_o,
    output logic [31:0]                          L2_icache_sel_flush_addr_o,
    input  logic [NB_CACHE_BANKS-1:0]            L2_icache_sel_flush_ack_i,

    output logic [NB_CORES-1:0]                  enable_l1_l15_prefetch_o

`ifdef FEATURE_ICACHE_STAT
    ,
    // L1 Counters
    input logic [NB_CORES-1:0] [31:0]                 L1_hit_count_i,
    input logic [NB_CORES-1:0] [31:0]                 L1_trans_count_i,
    input logic [NB_CORES-1:0] [31:0]                 L1_miss_count_i,
    input logic [NB_CORES-1:0] [31:0]                 L1_cong_count_i,

    output logic [NB_CORES-1:0]                       L1_clear_regs_o,
    output logic [NB_CORES-1:0]                       L1_enable_regs_o,

    // L2 Counters
    input logic [NB_CACHE_BANKS-1:0] [31:0]           L2_hit_count_i,
    input logic [NB_CACHE_BANKS-1:0] [31:0]           L2_trans_count_i,
    input logic [NB_CACHE_BANKS-1:0] [31:0]           L2_miss_count_i,

    output logic [NB_CACHE_BANKS-1:0]                 L2_clear_regs_o,
    output logic [NB_CACHE_BANKS-1:0]                 L2_enable_regs_o
`endif

);

   logic [NB_CACHE_BANKS+NB_CORES-1:0]                r_enable_icache;
   logic [NB_CACHE_BANKS+NB_CORES-1:0]                r_flush_icache;
   logic [31:0]                                       r_sel_flush_icache;

`ifdef FEATURE_ICACHE_STAT
   logic [NB_CACHE_BANKS+NB_CORES-1:0]                r_clear_cnt;
   logic [NB_CACHE_BANKS+NB_CORES-1:0]                r_enable_cnt;
`endif


    int unsigned  i,j,k,x,y;

    localparam BASE_PERF_CNT = 8;


    // State of the main FSM
`ifdef FEATURE_ICACHE_STAT
    enum logic [2:0] { IDLE, ENABLE_ICACHE,  DISABLE_ICACHE, FLUSH_ICACHE_CHECK, SEL_FLUSH_ICACHE, CLEAR_STAT_REGS, ENABLE_STAT_REGS } CS, NS;
`else
    enum logic [2:0] { IDLE, ENABLE_ICACHE,  DISABLE_ICACHE, FLUSH_ICACHE_CHECK, SEL_FLUSH_ICACHE } CS, NS;
`endif

    // Logic to Track the received acks on L1 PRI
    logic [NB_CORES-1:0]                 L1_mask_bypass_req_CS,    L1_mask_bypass_req_NS;
    logic [NB_CORES-1:0]                 L1_mask_flush_req_CS,     L1_mask_flush_req_NS;
    logic [NB_CORES-1:0]                 L1_mask_sel_flush_req_CS, L1_mask_sel_flush_req_NS;

    // Logic to Track the received acks on L2 SH
    logic [NB_CACHE_BANKS-1:0]           L2_mask_enable_req_CS,    L2_mask_enable_req_NS;
    logic [NB_CACHE_BANKS-1:0]           L2_mask_disable_req_CS,   L2_mask_disable_req_NS;
    logic [NB_CACHE_BANKS-1:0]           L2_mask_flush_req_CS,     L2_mask_flush_req_NS;
    logic [NB_CACHE_BANKS-1:0]           L2_mask_sel_flush_req_CS, L2_mask_sel_flush_req_NS;

    // Internal FSM signals --> responses
    logic                                 is_write;
    logic                                 deliver_response;
    logic                                 clear_flush_reg;

    logic [15:0][3:0][31:0]               perf_cnt_L1;
    logic [15:0][2:0][31:0]               perf_cnt_L2;



     genvar index;



   always_comb
   begin : REGISTER_BIND_OUT
      L1_icache_bypass_req_o     =  ~r_enable_icache[NB_CORES-1:0];
      L1_icache_sel_flush_addr_o =   r_sel_flush_icache;

      L2_icache_enable_req_o     =   r_enable_icache[NB_CACHE_BANKS+NB_CORES-1:NB_CORES];
      L2_icache_disable_req_o    =  ~r_enable_icache[NB_CACHE_BANKS+NB_CORES-1:NB_CORES];

      L2_icache_sel_flush_addr_o =   r_sel_flush_icache;

`ifdef FEATURE_ICACHE_STAT
      L1_enable_regs_o           =   r_enable_cnt[NB_CORES-1:0];
      L2_enable_regs_o           =   r_enable_cnt[NB_CACHE_BANKS+NB_CORES-1:NB_CORES];
`endif

   end




`ifdef FEATURE_ICACHE_STAT
   logic [31:0] global_L1_hit;
   logic [31:0] global_L1_trans;
   logic [31:0] global_L1_miss;
   logic [31:0] global_L1_cong;

   logic [31:0] global_L2_hit;
   logic [31:0] global_L2_trans;
   logic [31:0] global_L2_miss;


    always_comb
    begin
        global_L1_hit   = '0;
        global_L1_trans = '0;
        global_L1_miss  = '0;
        global_L1_cong  = '0;

        global_L2_hit   = '0;
        global_L2_trans = '0;
        global_L2_miss  = '0;

        for(int unsigned p=0; p<NB_CORES; p++)
        begin
            global_L1_hit   = global_L1_hit   + L1_hit_count_i[p];
            global_L1_trans = global_L1_trans + L1_trans_count_i[p];
            global_L1_miss  = global_L1_miss  + L1_miss_count_i[p];
            global_L1_cong  = global_L1_cong  + L1_cong_count_i[p];
        end

        for(int unsigned p=0; p<NB_CACHE_BANKS; p++)
        begin
            global_L2_hit   = global_L2_hit   + L2_hit_count_i[p];
            global_L2_trans = global_L2_trans + L2_trans_count_i[p];
            global_L2_miss  = global_L2_miss  + L2_miss_count_i[p];
        end
    end

`endif


generate


   logic [31:0] perf_cnt_enable;

`ifdef FEATURE_ICACHE_STAT
     assign perf_cnt_enable = { {(32-NB_CACHE_BANKS-NB_CORES){1'b0}}, {r_enable_cnt} };
     for(index=0; index<NB_CORES; index++)
     begin : PERF_CNT_BINDING

        always @(*)
        begin


          if(index<NB_CORES)
          begin
              perf_cnt_L1[index][0] = L1_hit_count_i   [index];
              perf_cnt_L1[index][1] = L1_trans_count_i [index];
              perf_cnt_L1[index][2] = L1_miss_count_i  [index];
              perf_cnt_L1[index][3] = L1_cong_count_i  [index];
          end
          else
          begin
              perf_cnt_L1[index][0] = 32'hBAD_ACCE5;
              perf_cnt_L1[index][1] = 32'hBAD_ACCE5;
              perf_cnt_L1[index][2] = 32'hBAD_ACCE5;
              perf_cnt_L1[index][3] = 32'hBAD_ACCE5;
          end

        end


        always @(*)
        begin

          if(index<NB_CACHE_BANKS)
          begin
              perf_cnt_L2[index][0] = L2_hit_count_i   [index];
              perf_cnt_L2[index][1] = L2_trans_count_i [index];
              perf_cnt_L2[index][2] = L2_miss_count_i  [index];
          end
          else
          begin
              perf_cnt_L2[index][0] = 32'hBAD_ACCE5;
              perf_cnt_L2[index][1] = 32'hBAD_ACCE5;
              perf_cnt_L2[index][2] = 32'hBAD_ACCE5;
          end

        end


     end //~for(index=0; index<16; index++)
 `else
    assign perf_cnt_enable = 32'hBAD_ACCE5;
 `endif





   always_ff @(posedge clk_i, negedge rst_ni)
   begin : SEQ_PROC
      if(rst_ni == 1'b0)
      begin
              CS                       <= IDLE;

              L1_mask_bypass_req_CS    <= '0;
              L1_mask_flush_req_CS     <= '0;
              L1_mask_sel_flush_req_CS <= '0;

              L2_mask_enable_req_CS    <= '0;
              L2_mask_disable_req_CS   <= '0;
              L2_mask_flush_req_CS     <= '0;
              L2_mask_sel_flush_req_CS <= '0;

              speriph_slave_r_id_o    <=   '0;
              speriph_slave_r_valid_o <= 1'b0;
              speriph_slave_r_rdata_o <=   '0;
              speriph_slave_r_opc_o   <= 1'b0;

              r_enable_icache    <=   '0;
              r_flush_icache     <=   '0;
              r_sel_flush_icache <=   '0;

`ifdef FEATURE_ICACHE_STAT
              r_clear_cnt        <=   '0;
              r_enable_cnt       <=   '0;
`endif
              enable_l1_l15_prefetch_o  <=  'h00;
      end
      else
      begin

        CS                       <= NS;

        L1_mask_bypass_req_CS    <= L1_mask_bypass_req_NS;
        L1_mask_flush_req_CS     <= L1_mask_flush_req_NS;
        L1_mask_sel_flush_req_CS <= L1_mask_sel_flush_req_NS;

        L2_mask_enable_req_CS    <= L2_mask_enable_req_NS;
        L2_mask_disable_req_CS   <= L2_mask_disable_req_NS;
        L2_mask_flush_req_CS     <= L2_mask_flush_req_NS;
        L2_mask_sel_flush_req_CS <= L2_mask_sel_flush_req_NS;

        if(is_write)
        begin
            if (speriph_slave_addr_i[7:2] == `ENABLE_ICACHE)  // ENABLE-DISABLE
                begin
                  r_enable_icache[NB_CORES+NB_CACHE_BANKS-1:0] <= {(NB_CORES+NB_CACHE_BANKS){speriph_slave_wdata_i[0]}};
                end

            else if (speriph_slave_addr_i[7:2] == `FLUSH_ICACHE) // FLUSH
                begin
                  r_flush_icache[NB_CORES+NB_CACHE_BANKS-1:0] <= {(NB_CORES+NB_CACHE_BANKS){speriph_slave_wdata_i[0]}};
                end

            else if(speriph_slave_addr_i[7:2] == `FLUSH_L1_ONLY) // FLUSH_L1_ONLY
                begin
                  r_flush_icache[NB_CORES+NB_CACHE_BANKS-1:0] <= {{(NB_CACHE_BANKS){1'b0}}, {(NB_CORES){speriph_slave_wdata_i[0]}} };
                end

            else if(speriph_slave_addr_i[7:2] == `SEL_FLUSH_ICACHE) // Sel FLUSH
                begin
                  r_sel_flush_icache <= speriph_slave_wdata_i;
                end

            `ifdef FEATURE_ICACHE_STAT
            else if(speriph_slave_addr_i[7:2] == `CLEAR_CNTS) // CLEAR
                begin
                  r_clear_cnt[NB_CORES+NB_CACHE_BANKS-1:0] <= {(NB_CORES+NB_CACHE_BANKS){speriph_slave_wdata_i[0]}};
                end

            else if(speriph_slave_addr_i[7:2] == `ENABLE_CNTS) // ENABLE-DISABLE STAT REGS
                begin
                  r_enable_cnt[NB_CORES+NB_CACHE_BANKS-1:0] <= {(NB_CORES+NB_CACHE_BANKS){speriph_slave_wdata_i[0]}};
                end
            `endif
            else if(speriph_slave_addr_i[7:2] == `ENABLE_L1_L15_PREFETCH) // enable l1 to l15 prefetch feature
                begin
                  enable_l1_l15_prefetch_o <= speriph_slave_wdata_i[NB_CORES-1:0];
                end

        end
        else // Not Write
        begin
            if(clear_flush_reg)
               r_flush_icache[NB_CORES+NB_CACHE_BANKS-1:0] <= { (NB_CORES+NB_CACHE_BANKS){1'b0} };
        end






        // sample the ID
        if(speriph_slave_req_i & speriph_slave_gnt_o)
        begin
          speriph_slave_r_id_o  <= speriph_slave_id_i;
        end


        //Handle register read
        if(deliver_response == 1'b1)
        begin
          speriph_slave_r_valid_o <= 1'b1;

          case(speriph_slave_addr_i[8:2])
          0:   begin speriph_slave_r_rdata_o       <= { {(32-NB_CACHE_BANKS-NB_CORES){1'b0}}, {r_enable_icache}     }; end
          1:   begin speriph_slave_r_rdata_o       <= { {(32-NB_CACHE_BANKS-NB_CORES){1'b0}}, {r_flush_icache}      }; end
          3:   begin speriph_slave_r_rdata_o       <= r_sel_flush_icache; end


          // Clear and start
          5:   begin speriph_slave_r_rdata_o       <= perf_cnt_enable;            end
          7:   begin speriph_slave_r_rdata_o       <= enable_l1_l15_prefetch_o;   end
          // BASE_PERF_CNT = 8
          (BASE_PERF_CNT+0):   begin speriph_slave_r_rdata_o       <= 32'hF1CA_B01A ;  end
          (BASE_PERF_CNT+1):   begin speriph_slave_r_rdata_o       <= 32'hF1CA_B01A ;  end
          (BASE_PERF_CNT+2):   begin speriph_slave_r_rdata_o       <= 32'hF1CA_B01A ;  end
          (BASE_PERF_CNT+3):   begin speriph_slave_r_rdata_o       <= 32'hF1CA_B01A ;  end

          (BASE_PERF_CNT+4):   begin speriph_slave_r_rdata_o       <= global_L1_hit;   end
          (BASE_PERF_CNT+5):   begin speriph_slave_r_rdata_o       <= global_L1_trans; end
          (BASE_PERF_CNT+6):   begin speriph_slave_r_rdata_o       <= global_L1_miss;  end
          (BASE_PERF_CNT+7):   begin speriph_slave_r_rdata_o       <= global_L1_cong;  end

          (BASE_PERF_CNT+8):   begin speriph_slave_r_rdata_o       <= global_L2_hit;   end
          (BASE_PERF_CNT+9):   begin speriph_slave_r_rdata_o       <= global_L2_trans; end
          (BASE_PERF_CNT+10):  begin speriph_slave_r_rdata_o       <= global_L2_miss;  end


          (BASE_PERF_CNT+12):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[0][0];  end
          (BASE_PERF_CNT+13):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[0][1];  end
          (BASE_PERF_CNT+14):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[0][2];  end
          (BASE_PERF_CNT+15):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[0][3];  end

          (BASE_PERF_CNT+16):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[1][0];  end
          (BASE_PERF_CNT+17):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[1][1];  end
          (BASE_PERF_CNT+18):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[1][2];  end
          (BASE_PERF_CNT+19):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[1][3];  end

          (BASE_PERF_CNT+20):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[2][0];  end
          (BASE_PERF_CNT+21):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[2][1];  end
          (BASE_PERF_CNT+22):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[2][2];  end
          (BASE_PERF_CNT+23):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[2][3];  end

          (BASE_PERF_CNT+24):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[3][0];  end
          (BASE_PERF_CNT+25):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[3][1];  end
          (BASE_PERF_CNT+26):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[3][2];  end
          (BASE_PERF_CNT+27):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[3][3];  end

          (BASE_PERF_CNT+28):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[4][0];  end
          (BASE_PERF_CNT+29):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[4][1];  end
          (BASE_PERF_CNT+30):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[4][2];  end
          (BASE_PERF_CNT+31):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[4][3];  end

          (BASE_PERF_CNT+32):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[5][0];  end
          (BASE_PERF_CNT+33):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[5][1];  end
          (BASE_PERF_CNT+34):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[5][2];  end
          (BASE_PERF_CNT+35):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[5][3];  end

          (BASE_PERF_CNT+36):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[6][0];  end
          (BASE_PERF_CNT+37):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[6][1];  end
          (BASE_PERF_CNT+38):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[6][2];  end
          (BASE_PERF_CNT+39):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[6][3];  end

          (BASE_PERF_CNT+40):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[7][0];  end
          (BASE_PERF_CNT+41):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[7][1];  end
          (BASE_PERF_CNT+42):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[7][2];  end
          (BASE_PERF_CNT+43):  begin speriph_slave_r_rdata_o       <= perf_cnt_L1[7][3];  end

          (BASE_PERF_CNT+44):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[0][0]; end
          (BASE_PERF_CNT+45):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[0][1]; end
          (BASE_PERF_CNT+46):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[0][2]; end

          (BASE_PERF_CNT+47):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[1][0]; end
          (BASE_PERF_CNT+48):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[1][1]; end
          (BASE_PERF_CNT+49):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[1][2]; end

          (BASE_PERF_CNT+50):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[2][0]; end
          (BASE_PERF_CNT+51):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[2][1]; end
          (BASE_PERF_CNT+52):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[2][2]; end

          (BASE_PERF_CNT+53):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[3][0]; end
          (BASE_PERF_CNT+54):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[3][1]; end
          (BASE_PERF_CNT+55):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[3][2]; end

          (BASE_PERF_CNT+56):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[4][0]; end
          (BASE_PERF_CNT+57):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[4][1]; end
          (BASE_PERF_CNT+58):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[4][2]; end

          (BASE_PERF_CNT+59):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[5][0]; end
          (BASE_PERF_CNT+60):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[5][1]; end
          (BASE_PERF_CNT+61):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[5][2]; end

          (BASE_PERF_CNT+62):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[6][0]; end
          (BASE_PERF_CNT+63):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[6][1]; end
          (BASE_PERF_CNT+64):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[6][2]; end

          (BASE_PERF_CNT+65):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[7][0]; end
          (BASE_PERF_CNT+66):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[7][1]; end
          (BASE_PERF_CNT+67):  begin speriph_slave_r_rdata_o       <= perf_cnt_L2[7][2]; end


          default : begin speriph_slave_r_rdata_o <= 32'hDEAD_CA5E; end
          endcase

          speriph_slave_r_opc_o   <= 1'b0;
        end
        else //nothing to Do
        begin
                  speriph_slave_r_valid_o <= 1'b0;
                  speriph_slave_r_opc_o   <= 1'b0;
        end

      end
   end

endgenerate







   always_comb
   begin
        // SPER SIDE
        speriph_slave_gnt_o    = 1'b0;

        is_write               = 1'b0;
        deliver_response       = 1'b0;

        L1_icache_sel_flush_req_o = '0;
        L2_icache_sel_flush_req_o = '0;

        clear_flush_reg           = 1'b0;

        L1_mask_bypass_req_NS     = L1_mask_bypass_req_CS;
        L1_mask_flush_req_NS      = L1_mask_flush_req_CS;
        L1_mask_sel_flush_req_NS  = L1_mask_sel_flush_req_CS;

        L2_mask_sel_flush_req_NS  = L2_mask_sel_flush_req_CS;
        L2_mask_enable_req_NS     = L2_mask_enable_req_CS;
        L2_mask_disable_req_NS    = L2_mask_disable_req_CS;
        L2_mask_flush_req_NS      = L2_mask_flush_req_CS;

        L2_icache_flush_req_o     =   '0;
        L1_icache_flush_req_o     =   '0;

        L1_icache_sel_flush_req_o = '0;
        L2_icache_sel_flush_req_o = '0;

`ifdef FEATURE_ICACHE_STAT
        L1_clear_regs_o          = '0;
        L2_clear_regs_o          = '0;
`endif

        case(CS)

          IDLE:
          begin
              speriph_slave_gnt_o = 1'b1;

              if(speriph_slave_req_i)
              begin
                if(speriph_slave_wen_i == 1'b1) // read
                begin
                      NS               = IDLE;
                      deliver_response = 1'b1;
                end
                else // Write registers
                begin

                      is_write = 1'b1;
                      NS = IDLE;

                      case(speriph_slave_addr_i[7:2])

                            `ENABLE_ICACHE: // Enable - Disable register
                            begin
                                if( speriph_slave_wdata_i[0] == 1'b0 )
                                begin
                                  NS = DISABLE_ICACHE;
                                  L1_mask_bypass_req_NS  = L1_icache_bypass_req_o;
                                  L2_mask_disable_req_NS = L2_icache_disable_req_o;
                                end
                                else
                                begin
                                  NS = ENABLE_ICACHE;
                                  L1_mask_bypass_req_NS =  L1_icache_bypass_req_o;
                                  L2_mask_enable_req_NS =  L2_icache_enable_req_o;
                                end
                            end //~2'b00

                            `FLUSH_ICACHE:
                            begin
                              NS = FLUSH_ICACHE_CHECK;
                              L1_mask_flush_req_NS = ~{(NB_CORES){speriph_slave_wdata_i[0]}};
                              L2_mask_flush_req_NS = ~{(NB_CACHE_BANKS){speriph_slave_wdata_i[0]}};
                            end

                            `FLUSH_L1_ONLY:
                            begin
                              NS = FLUSH_ICACHE_CHECK;
                              L1_mask_flush_req_NS = ~{(NB_CORES){speriph_slave_wdata_i[0]}};
                              L2_mask_flush_req_NS = '1;
                            end

                            `SEL_FLUSH_ICACHE:
                            begin
                              NS = SEL_FLUSH_ICACHE;
                              L1_mask_sel_flush_req_NS = L1_icache_sel_flush_req_o;
                              L2_mask_sel_flush_req_NS = L2_icache_sel_flush_req_o;
                            end


                        `ifdef FEATURE_ICACHE_STAT
                            `CLEAR_CNTS: // CLEAR
                            begin
                              NS = CLEAR_STAT_REGS;
                            end

                            `ENABLE_CNTS: // START
                            begin
                              NS = ENABLE_STAT_REGS;
                            end
                        `endif

                             `ENABLE_BYPASS: // Enable BYPASS
                              begin
                                deliver_response = 1'b1;
                                NS = IDLE;
                              end

                             `ENABLE_L1_L15_PREFETCH: // Enable L1_L15
                              begin
                                deliver_response = 1'b1;
                                NS = IDLE;
                              end
                      endcase

                end

              end
              else // no request
              begin
                  NS = IDLE;
              end

          end //~IDLE

`ifdef FEATURE_ICACHE_STAT
          CLEAR_STAT_REGS:
          begin
             for(x=0; x<NB_CORES; x++)
             begin
                L1_clear_regs_o[x]  =   r_clear_cnt[x];
             end

             for(x=0; x<NB_CACHE_BANKS; x++)
             begin
                L2_clear_regs_o[x]  =   r_clear_cnt[x+NB_CORES];
             end


             deliver_response = 1'b1;
             NS = IDLE;
          end //~ CLEAR_STAT_REGS


          ENABLE_STAT_REGS:
          begin

             deliver_response = 1'b1;
             NS = IDLE;
          end //~ENABLE_STAT_REGS
`endif





          ENABLE_ICACHE:
          begin
            speriph_slave_gnt_o = 1'b0;
            L1_mask_bypass_req_NS = L1_icache_bypass_ack_i & L1_mask_bypass_req_CS;
            L2_mask_enable_req_NS = L2_icache_enable_ack_i | L2_mask_enable_req_CS;



            if( ((L1_icache_bypass_ack_i | L1_mask_bypass_req_CS) == '0 )  &&  ((L2_icache_enable_ack_i | L2_mask_enable_req_CS) == '1)  ) //11111 --> all enabled; 00000 --> all enabled
            begin
              NS = IDLE;
              deliver_response = 1'b1;
            end
            else
            begin
              NS = ENABLE_ICACHE;
            end
          end //~ENABLE_ICACHE






          DISABLE_ICACHE:
          begin
            speriph_slave_gnt_o = 1'b0;

            L1_mask_bypass_req_NS  = L1_icache_bypass_ack_i  | L1_mask_bypass_req_CS;
            L2_mask_disable_req_NS = L2_icache_disable_ack_i | L2_mask_disable_req_CS;

            //if(  &({L2_icache_disable_ack_i,L1_icache_bypass_ack_i} | {L2_mask_disable_req_CS, L1_mask_bypass_req_CS}  ) ) //11111 --> all bypassed; 00000 --> all enabled
            if(  (&(L2_icache_disable_ack_i | L2_mask_disable_req_CS))  &&     (&(L1_mask_bypass_req_CS | L1_icache_bypass_ack_i ))  )
            begin
              NS = IDLE;
              deliver_response = 1'b1;
            end
            else
            begin
              NS = DISABLE_ICACHE;
            end
          end //~DIABLE_ICACHE


          FLUSH_ICACHE_CHECK:
          begin
              speriph_slave_gnt_o = 1'b0;
              L1_mask_flush_req_NS = L1_icache_flush_ack_i | L1_mask_flush_req_CS;
              L2_mask_flush_req_NS = L2_icache_flush_ack_i | L2_mask_flush_req_CS;
              L2_icache_flush_req_o     =  r_flush_icache[NB_CACHE_BANKS+NB_CORES-1:NB_CORES] & (~L2_mask_flush_req_CS);
              L1_icache_flush_req_o     =  r_flush_icache[NB_CORES-1:0] & (~L1_mask_flush_req_CS);

              if(  &{ L2_mask_flush_req_CS , L1_mask_flush_req_CS } )
              begin
                 NS = IDLE;
                 deliver_response = 1'b1;
                 clear_flush_reg  = 1'b1;
              end
              else
              begin
                NS = FLUSH_ICACHE_CHECK;
              end
          end


          SEL_FLUSH_ICACHE:
          begin

              L2_mask_sel_flush_req_NS = L2_mask_sel_flush_req_CS | L2_icache_sel_flush_ack_i;
              L1_mask_sel_flush_req_NS = L1_mask_sel_flush_req_CS | L1_icache_sel_flush_ack_i;
              L1_icache_sel_flush_req_o = ~L1_mask_sel_flush_req_CS;
              L2_icache_sel_flush_req_o = ~L2_mask_sel_flush_req_CS;

              if( &{ L2_mask_sel_flush_req_CS, L1_mask_sel_flush_req_CS } )
              begin
                speriph_slave_gnt_o = 1'b1;
                NS  = IDLE;
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
