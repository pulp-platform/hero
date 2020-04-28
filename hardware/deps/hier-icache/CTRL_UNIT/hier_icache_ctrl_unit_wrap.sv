// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


`define FEATURE_ICACHE_STAT

module hier_icache_ctrl_unit_wrap
#(
    parameter  NB_CACHE_BANKS = 4,
    parameter  NB_CORES       = 9,
    parameter  ID_WIDTH       = 5
)
(
    input logic                                 clk_i,
    input logic                                 rst_ni,

    XBAR_PERIPH_BUS.Slave                       speriph_slave,

    SP_ICACHE_CTRL_UNIT_BUS.Master              IC_ctrl_unit_bus_main[NB_CACHE_BANKS],
    PRI_ICACHE_CTRL_UNIT_BUS.Master             IC_ctrl_unit_bus_pri[NB_CORES],
    output logic [NB_CORES-1:0]                 enable_l1_l15_prefetch_o

);

   logic [NB_CORES-1:0]                         IC_ctrl_unit_bus_pri_bypass_req;
   logic [NB_CORES-1:0]                         IC_ctrl_unit_bus_pri_bypass_ack;
   logic [NB_CORES-1:0]                         IC_ctrl_unit_bus_pri_flush_req;
   logic [NB_CORES-1:0]                         IC_ctrl_unit_bus_pri_flush_ack;
   logic [NB_CORES-1:0]                         IC_ctrl_unit_bus_pri_sel_flush_req;
   logic [31:0]                                 IC_ctrl_unit_bus_pri_sel_flush_addr;
   logic [NB_CORES-1:0]                         IC_ctrl_unit_bus_pri_sel_flush_ack;

   logic [NB_CACHE_BANKS-1:0]                   IC_ctrl_unit_bus_main_enable_req;
   logic [NB_CACHE_BANKS-1:0]                   IC_ctrl_unit_bus_main_enable_ack;
   logic [NB_CACHE_BANKS-1:0]                   IC_ctrl_unit_bus_main_disable_req;
   logic [NB_CACHE_BANKS-1:0]                   IC_ctrl_unit_bus_main_disable_ack;
   logic [NB_CACHE_BANKS-1:0]                   IC_ctrl_unit_bus_main_flush_req;
   logic [NB_CACHE_BANKS-1:0]                   IC_ctrl_unit_bus_main_flush_ack;
   logic [NB_CACHE_BANKS-1:0]                   IC_ctrl_unit_bus_main_sel_flush_req;
   logic [31:0]                                 IC_ctrl_unit_bus_main_sel_flush_addr;
   logic [NB_CACHE_BANKS-1:0]                   IC_ctrl_unit_bus_main_sel_flush_ack;

`ifdef FEATURE_ICACHE_STAT
    // L1 Counters
    logic [NB_CORES-1:0] [31:0]                 IC_ctrl_unit_bus_pri_L1_hit_count;
    logic [NB_CORES-1:0] [31:0]                 IC_ctrl_unit_bus_pri_L1_trans_count;
    logic [NB_CORES-1:0] [31:0]                 IC_ctrl_unit_bus_pri_L1_miss_count;
    logic [NB_CORES-1:0] [31:0]                 IC_ctrl_unit_bus_pri_L1_cong_count;
    logic [NB_CORES-1:0]                        IC_ctrl_unit_bus_pri_L1_clear_regs;
    logic [NB_CORES-1:0]                        IC_ctrl_unit_bus_pri_L1_enable_regs;

    // L2 Counters
    logic [NB_CACHE_BANKS-1:0] [31:0]           IC_ctrl_unit_bus_main_L2_hit_count;
    logic [NB_CACHE_BANKS-1:0] [31:0]           IC_ctrl_unit_bus_main_L2_trans_count;
    logic [NB_CACHE_BANKS-1:0] [31:0]           IC_ctrl_unit_bus_main_L2_miss_count;
    logic [NB_CACHE_BANKS-1:0]                  IC_ctrl_unit_bus_main_L2_clear_regs;
    logic [NB_CACHE_BANKS-1:0]                  IC_ctrl_unit_bus_main_L2_enable_regs;
`endif 

   genvar i;
   generate
      for(i=0;i<NB_CORES;i++)
      begin
         assign  IC_ctrl_unit_bus_pri[i].bypass_req     = IC_ctrl_unit_bus_pri_bypass_req[i];
         assign  IC_ctrl_unit_bus_pri_bypass_ack[i]     = IC_ctrl_unit_bus_pri[i].bypass_ack; 

         assign  IC_ctrl_unit_bus_pri[i].flush_req      = IC_ctrl_unit_bus_pri_flush_req[i];
         assign  IC_ctrl_unit_bus_pri_flush_ack[i]      = IC_ctrl_unit_bus_pri[i].flush_ack;

         assign  IC_ctrl_unit_bus_pri[i].sel_flush_req  = IC_ctrl_unit_bus_pri_sel_flush_req  [i] ;
         assign  IC_ctrl_unit_bus_pri[i].sel_flush_addr = IC_ctrl_unit_bus_pri_sel_flush_addr ;
         assign  IC_ctrl_unit_bus_pri_sel_flush_ack[i]  = IC_ctrl_unit_bus_pri[i].sel_flush_ack;
`ifdef FEATURE_ICACHE_STAT
         assign IC_ctrl_unit_bus_pri_L1_hit_count   [i]   = IC_ctrl_unit_bus_pri[i].ctrl_hit_count;
         assign IC_ctrl_unit_bus_pri_L1_trans_count [i]   = IC_ctrl_unit_bus_pri[i].ctrl_trans_count;
         assign IC_ctrl_unit_bus_pri_L1_miss_count  [i]   = IC_ctrl_unit_bus_pri[i].ctrl_miss_count;
         assign IC_ctrl_unit_bus_pri_L1_cong_count  [i]   = IC_ctrl_unit_bus_pri[i].ctrl_cong_count;
         
         assign IC_ctrl_unit_bus_pri[i].ctrl_clear_regs   = IC_ctrl_unit_bus_pri_L1_clear_regs   [i] ;
         assign IC_ctrl_unit_bus_pri[i].ctrl_enable_regs  = IC_ctrl_unit_bus_pri_L1_enable_regs  [i] ;
`endif         
      end

      for(i=0;i<NB_CACHE_BANKS;i++)
      begin
         assign  IC_ctrl_unit_bus_main[i].ctrl_req_enable = IC_ctrl_unit_bus_main_enable_req[i];
         assign  IC_ctrl_unit_bus_main_enable_ack[i]      = IC_ctrl_unit_bus_main[i].ctrl_ack_enable;

         assign  IC_ctrl_unit_bus_main[i].ctrl_req_disable = IC_ctrl_unit_bus_main_disable_req[i];
         assign  IC_ctrl_unit_bus_main_disable_ack[i]      = IC_ctrl_unit_bus_main[i].ctrl_ack_disable;

         assign  IC_ctrl_unit_bus_main[i].ctrl_flush_req   = IC_ctrl_unit_bus_main_flush_req[i];
         assign  IC_ctrl_unit_bus_main_flush_ack[i]        = IC_ctrl_unit_bus_main[i].ctrl_flush_ack;

         assign  IC_ctrl_unit_bus_main[i].icache_is_private = 1'b1;

         assign  IC_ctrl_unit_bus_main[i].sel_flush_req     = IC_ctrl_unit_bus_main_sel_flush_req  [i];
         assign  IC_ctrl_unit_bus_main[i].sel_flush_addr    = IC_ctrl_unit_bus_main_sel_flush_addr;
         assign  IC_ctrl_unit_bus_main_sel_flush_ack[i]     = IC_ctrl_unit_bus_main[i].sel_flush_ack;

`ifdef FEATURE_ICACHE_STAT
         assign IC_ctrl_unit_bus_main_L2_hit_count    [i]  = IC_ctrl_unit_bus_main[i].ctrl_hit_count;
         assign IC_ctrl_unit_bus_main_L2_trans_count  [i]  = IC_ctrl_unit_bus_main[i].ctrl_trans_count;
         assign IC_ctrl_unit_bus_main_L2_miss_count   [i]  = IC_ctrl_unit_bus_main[i].ctrl_miss_count;
         assign IC_ctrl_unit_bus_main[i].ctrl_clear_regs   = IC_ctrl_unit_bus_main_L2_clear_regs   [i] ;
         assign IC_ctrl_unit_bus_main[i].ctrl_enable_regs  = IC_ctrl_unit_bus_main_L2_enable_regs  [i] ;
`endif         
      end

   endgenerate

   hier_icache_ctrl_unit
   #(
       .NB_CACHE_BANKS ( NB_CACHE_BANKS ), //= 4,
       .NB_CORES       ( NB_CORES       ), //= 8,
       .ID_WIDTH       ( ID_WIDTH       )  //= 5
   )
   i_hier_icache_ctrl_unit
   (
       .clk_i                       (  clk_i   ),
       .rst_ni                      (  rst_ni  ),

       // Exploded Interface --> PERIPHERAL INTERFACE
       .speriph_slave_req_i         (  speriph_slave.req        ),
       .speriph_slave_addr_i        (  speriph_slave.add        ),
       .speriph_slave_wen_i         (  speriph_slave.wen        ),
       .speriph_slave_wdata_i       (  speriph_slave.wdata      ),
       .speriph_slave_be_i          (  speriph_slave.be         ),
       .speriph_slave_gnt_o         (  speriph_slave.gnt        ),
       .speriph_slave_id_i          (  speriph_slave.id         ),
       .speriph_slave_r_valid_o     (  speriph_slave.r_valid    ),
       .speriph_slave_r_opc_o       (  speriph_slave.r_opc      ),
       .speriph_slave_r_id_o        (  speriph_slave.r_id       ),
       .speriph_slave_r_rdata_o     (  speriph_slave.r_rdata    ),

       .L1_icache_bypass_req_o      (  IC_ctrl_unit_bus_pri_bypass_req      ),
       .L1_icache_bypass_ack_i      (  IC_ctrl_unit_bus_pri_bypass_ack      ),
       .L1_icache_flush_req_o       (  IC_ctrl_unit_bus_pri_flush_req       ),
       .L1_icache_flush_ack_i       (  IC_ctrl_unit_bus_pri_flush_ack       ),
       .L1_icache_sel_flush_req_o   (  IC_ctrl_unit_bus_pri_sel_flush_req   ),
       .L1_icache_sel_flush_addr_o  (  IC_ctrl_unit_bus_pri_sel_flush_addr  ),
       .L1_icache_sel_flush_ack_i   (  IC_ctrl_unit_bus_pri_sel_flush_ack   ),

       .L2_icache_enable_req_o      (  IC_ctrl_unit_bus_main_enable_req      ),
       .L2_icache_enable_ack_i      (  IC_ctrl_unit_bus_main_enable_ack      ),
       .L2_icache_disable_req_o     (  IC_ctrl_unit_bus_main_disable_req     ),
       .L2_icache_disable_ack_i     (  IC_ctrl_unit_bus_main_disable_ack     ),
       .L2_icache_flush_req_o       (  IC_ctrl_unit_bus_main_flush_req       ),
       .L2_icache_flush_ack_i       (  IC_ctrl_unit_bus_main_flush_ack       ),
       .L2_icache_sel_flush_req_o   (  IC_ctrl_unit_bus_main_sel_flush_req   ),
       .L2_icache_sel_flush_addr_o  (  IC_ctrl_unit_bus_main_sel_flush_addr  ),
       .L2_icache_sel_flush_ack_i   (  IC_ctrl_unit_bus_main_sel_flush_ack   ),
       .enable_l1_l15_prefetch_o    ( enable_l1_l15_prefetch_o               )



   `ifdef FEATURE_ICACHE_STAT
       ,
       .L1_hit_count_i              ( IC_ctrl_unit_bus_pri_L1_hit_count    ),
       .L1_trans_count_i            ( IC_ctrl_unit_bus_pri_L1_trans_count  ),
       .L1_miss_count_i             ( IC_ctrl_unit_bus_pri_L1_miss_count   ),
       .L1_cong_count_i             ( IC_ctrl_unit_bus_pri_L1_cong_count   ),
       .L1_clear_regs_o             ( IC_ctrl_unit_bus_pri_L1_clear_regs   ),
       .L1_enable_regs_o            ( IC_ctrl_unit_bus_pri_L1_enable_regs  ),

       .L2_hit_count_i              ( IC_ctrl_unit_bus_main_L2_hit_count   ),
       .L2_trans_count_i            ( IC_ctrl_unit_bus_main_L2_trans_count ),
       .L2_miss_count_i             ( IC_ctrl_unit_bus_main_L2_miss_count  ),
       .L2_clear_regs_o             ( IC_ctrl_unit_bus_main_L2_clear_regs  ),
       .L2_enable_regs_o            ( IC_ctrl_unit_bus_main_L2_enable_regs )
   `endif

   );


endmodule // hier_icache_ctrl_unit
