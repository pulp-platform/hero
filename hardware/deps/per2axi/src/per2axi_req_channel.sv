// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Davide Rossi <davide.rossi@unibo.it>

import riscv_defines::*;

module per2axi_req_channel
#(
   // PARAMETERS
   parameter NB_CORES       = 4,
   parameter PER_ADDR_WIDTH = 32,
   parameter PER_ID_WIDTH   = 5,
   parameter AXI_ADDR_WIDTH = 32,
   parameter AXI_DATA_WIDTH = 64,
   parameter AXI_USER_WIDTH = 6,
   parameter AXI_ID_WIDTH   = 3,
   parameter bit EN_TRYX = 1'b0,
   parameter type tryx_req_t = logic,
   // LOCAL PARAMETERS --> DO NOT OVERRIDE
   parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH/8 // DO NOT OVERRIDE
)
(
   input  logic                      clk_i,
   input  logic                      rst_ni,

   // PERIPHERAL INTERCONNECT SLAVE
   //***************************************
   //REQUEST CHANNEL
   input  logic                      per_slave_req_i,
   input  logic [PER_ADDR_WIDTH-1:0] per_slave_add_i,
   input  logic                      per_slave_we_i,
   input  logic [5:0]                per_slave_atop_i,
   input  logic [31:0]               per_slave_wdata_i,
   input  logic [3:0]                per_slave_be_i,
   input  logic [PER_ID_WIDTH-1:0]   per_slave_id_i,
   output logic                      per_slave_gnt_o,

   // TRYX CTRL
   input  tryx_req_t [NB_CORES-1:0]  tryx_req_i,

   // AXI4 MASTER
   //***************************************
   // WRITE ADDRESS CHANNEL
   output logic                      axi_master_aw_valid_o,
   output logic [AXI_ADDR_WIDTH-1:0] axi_master_aw_addr_o,
   output logic [2:0]                axi_master_aw_prot_o,
   output logic [3:0]                axi_master_aw_region_o,
   output logic [7:0]                axi_master_aw_len_o,
   output logic [2:0]                axi_master_aw_size_o,
   output logic [1:0]                axi_master_aw_burst_o,
   output logic                      axi_master_aw_lock_o,
   output logic [5:0]                axi_master_aw_atop_o,
   output logic [3:0]                axi_master_aw_cache_o,
   output logic [3:0]                axi_master_aw_qos_o,
   output logic [AXI_ID_WIDTH-1:0]   axi_master_aw_id_o,
   output logic [AXI_USER_WIDTH-1:0] axi_master_aw_user_o,
   input  logic                      axi_master_aw_ready_i,

   // READ ADDRESS CHANNEL
   output logic                      axi_master_ar_valid_o,
   output logic [AXI_ADDR_WIDTH-1:0] axi_master_ar_addr_o,
   output logic [2:0]                axi_master_ar_prot_o,
   output logic [3:0]                axi_master_ar_region_o,
   output logic [7:0]                axi_master_ar_len_o,
   output logic [2:0]                axi_master_ar_size_o,
   output logic [1:0]                axi_master_ar_burst_o,
   output logic                      axi_master_ar_lock_o,
   output logic [3:0]                axi_master_ar_cache_o,
   output logic [3:0]                axi_master_ar_qos_o,
   output logic [AXI_ID_WIDTH-1:0]   axi_master_ar_id_o,
   output logic [AXI_USER_WIDTH-1:0] axi_master_ar_user_o,
   input  logic                      axi_master_ar_ready_i,

   // WRITE DATA CHANNEL
   output logic                      axi_master_w_valid_o,
   output logic [AXI_DATA_WIDTH-1:0] axi_master_w_data_o,
   output logic [AXI_STRB_WIDTH-1:0] axi_master_w_strb_o,
   output logic [AXI_USER_WIDTH-1:0] axi_master_w_user_o,
   output logic                      axi_master_w_last_o,
   input  logic                      axi_master_w_ready_i,

   // CONTROL SIGNALS
   output logic                      atop_req_o,
   output logic [AXI_ID_WIDTH-1:0]   atop_id_o,
   output logic [AXI_ADDR_WIDTH-1:0] atop_add_o,

   output logic                      trans_req_o,
   output logic [AXI_ID_WIDTH-1:0]   trans_id_o,
   output logic [AXI_ADDR_WIDTH-1:0] trans_add_o
);

   integer                            i;

   assign axi_master_aw_atop_o = '0;

   // AXI REQUEST GENERATION
   always_comb
     begin
        axi_master_ar_valid_o = 1'b0;
        axi_master_aw_valid_o = 1'b0;
        axi_master_w_valid_o  = 1'b0;
        axi_master_w_last_o   = 1'b0;

        if (per_slave_req_i == 1'b1 &&       // REQUEST FROM PERIPHERAL INTERCONNECT
            per_slave_we_i == 1'b0 &&        // WRITE OPERATION
            axi_master_aw_ready_i == 1'b1 && // AXI WRITE ADDRESS CHANNEL AVAILABLE
            axi_master_w_ready_i == 1'b1 )   // AXI WRITE DATA CHANNEL AVAILABLE
          begin
             axi_master_aw_valid_o = 1'b1;
             axi_master_w_valid_o  = 1'b1;
             axi_master_w_last_o   = 1'b1;
          end
        else
          if (per_slave_req_i == 1'b1 &&     // REQUEST FROM PERIPHERAL INTERCONNECT
              per_slave_we_i == 1'b1 &&      // READ OPERATION
              axi_master_ar_ready_i == 1'b1) // AXI WRITE ADDRESS CHANNEL AVAILABLE
            begin
               axi_master_ar_valid_o = 1'b1;
            end
     end

    // AXI ATOMIC ACCESS LOCK GENERATION
    always_comb
    begin
        axi_master_aw_lock_o   = 1'b0;
        axi_master_ar_lock_o   = 1'b0;
        axi_master_aw_addr_o   = per_slave_add_i;

        if (per_slave_atop_i[5] == 1'b1) begin
            unique case (per_slave_atop_i[4:0])
                AMO_LR: begin                       // ATOMIC LOAD-RESERVED OPERATION
                    axi_master_ar_lock_o = 1'b1;
                end
                AMO_SC: begin                       // ATOMIC STORE-CONDITIONAL OPERATION
                    axi_master_aw_lock_o = 1'b1;
                end
                AMO_SWAP,
                AMO_ADD,
                AMO_XOR,
                AMO_AND,
                AMO_OR,
                AMO_MIN,
                AMO_MAX,
                AMO_MINU,
                AMO_MAXU: begin
                    // Redirect atomic operations to error slave in SoC bus.
                    axi_master_aw_addr_o = 32'h1B00_0000 + per_slave_add_i[11:0];
                end
                default: ;
            endcase
        end
    end

   // AXI ID GENERATION - ONEHOT TO BIN DECODING
   always_comb
     begin
        axi_master_aw_id_o = '0;
        axi_master_ar_id_o = '0;
        for ( i=0; i<PER_ID_WIDTH; i++ )
          begin
             if ( per_slave_id_i[i] == 1'b1 )
               begin
                  axi_master_aw_id_o = i;
                  axi_master_ar_id_o = i;
               end
          end
     end


   // AXI WRITE DATA/STROBE GENERATION
   always_comb
     begin
        if ( per_slave_add_i[2] == 1'b0 )
          begin
             axi_master_w_data_o = {32'b0,per_slave_wdata_i};
             axi_master_w_strb_o = {4'b0,per_slave_be_i};
          end
        else
          begin
             axi_master_w_data_o = {per_slave_wdata_i,32'b0};
             axi_master_w_strb_o = {per_slave_be_i,4'b0};
          end
     end

   // PERIPHERAL INTERCONNECT GRANT GENERATION
   assign per_slave_gnt_o = axi_master_aw_ready_i && axi_master_ar_ready_i && axi_master_w_ready_i;

   always_comb begin
      if (per_slave_be_i == (1 << per_slave_add_i[1:0])) begin
         axi_master_aw_size_o = 3'd0;
      end else if (per_slave_add_i[1:0] == 2'b00 && per_slave_be_i == 4'b0011
         || per_slave_add_i[1:0] == 2'b10 && per_slave_be_i == 4'b1100) begin
         axi_master_aw_size_o = 3'd1;
      end else begin
         axi_master_aw_size_o = 3'd2;
      end
   end
   assign axi_master_ar_size_o = axi_master_aw_size_o;

   // Assumptions
   `ifndef TARGET_SYNTHESIS
      default disable iff (!rst_ni);
      assume property (@(posedge clk_i) per_slave_req_i |-> per_slave_be_i[per_slave_add_i[1:0]])
         else $error("Byte enable of addressed byte must be active");
      logic [1:0] be_trailing_zeros;
      lzc #(
         .WIDTH   (4),
         .MODE    (1'b0)
      ) i_lzc_be_trailing (
         .in_i    (per_slave_be_i),
         .cnt_o   (be_trailing_zeros),
         .empty_o (/* unused */)
      );
      assume property (@(posedge clk_i) per_slave_req_i
            |-> per_slave_add_i[1:0] == be_trailing_zeros)
         else $error("No byte enable below addressed byte may be active!");
   `endif

   // use INCR burst type, length is anyway 0
   assign axi_master_aw_burst_o = axi_pkg::BURST_INCR;
   assign axi_master_ar_burst_o = axi_pkg::BURST_INCR;

   // TRANSACTION REQUEST GENERATION
   assign trans_req_o = axi_master_ar_valid_o;
   assign trans_id_o  = axi_master_ar_id_o;
   assign trans_add_o = axi_master_ar_addr_o;

   assign axi_master_ar_addr_o = per_slave_add_i;

   assign atop_req_o  = 1'b0;
   assign atop_id_o   = '0;
   assign atop_add_o  = '0;

   // UNUSED SIGNALS
   assign axi_master_aw_prot_o   = '0;
   assign axi_master_aw_region_o = '0;
   assign axi_master_aw_len_o    = '0;
   assign axi_master_aw_cache_o  = 4'b0000;
   assign axi_master_aw_qos_o    = '0;
   if (EN_TRYX) begin : gen_tryx_aw_user
      assign axi_master_aw_user_o = tryx_req_i[axi_master_aw_id_o].user;
   end else begin : gen_no_tryx_aw_user
      assign axi_master_aw_user_o = '0;
   end

   assign axi_master_ar_prot_o   = '0;
   assign axi_master_ar_region_o = '0;
   assign axi_master_ar_len_o    = '0;
   assign axi_master_ar_cache_o  = 4'b0000;
   assign axi_master_ar_qos_o    = '0;
   if (EN_TRYX) begin : gen_tryx_ar_user
      assign axi_master_ar_user_o = tryx_req_i[axi_master_ar_id_o].user;
   end else begin : gen_no_tryx_ar_user
      assign axi_master_ar_user_o = '0;
   end

   assign axi_master_w_user_o    = '0;

endmodule
