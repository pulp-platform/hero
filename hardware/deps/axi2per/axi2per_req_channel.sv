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

module axi2per_req_channel #(
  // PARAMETERS
  parameter PER_ADDR_WIDTH = 32,
  parameter PER_ID_WIDTH   = 5,
  parameter AXI_ADDR_WIDTH = 32,
  parameter AXI_DATA_WIDTH = 64,
  parameter AXI_USER_WIDTH = 6,
  parameter AXI_ID_WIDTH   = 3,
  // LOCAL PARAMETERS --> DO NOT OVERRIDE
  parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH/8 // DO NOT OVERRIDE
) (
  input logic                       clk_i,
  input logic                       rst_ni,

  input  logic [5:0]                cluster_id_i,

  input  logic                      axi_slave_aw_valid_i,
  input  logic [AXI_ADDR_WIDTH-1:0] axi_slave_aw_addr_i,
  input  logic [2:0]                axi_slave_aw_prot_i,
  input  logic [3:0]                axi_slave_aw_region_i,
  input  logic [7:0]                axi_slave_aw_len_i,
  input  logic [2:0]                axi_slave_aw_size_i,
  input  logic [1:0]                axi_slave_aw_burst_i,
  input  logic                      axi_slave_aw_lock_i,
  input  logic [5:0]                axi_slave_aw_atop_i,
  input  logic [3:0]                axi_slave_aw_cache_i,
  input  logic [3:0]                axi_slave_aw_qos_i,
  input  logic [AXI_ID_WIDTH-1:0]   axi_slave_aw_id_i,
  input  logic [AXI_USER_WIDTH-1:0] axi_slave_aw_user_i,
  output logic                      axi_slave_aw_ready_o,

  // READ ADDRESS CHANNEL
  input  logic                      axi_slave_ar_valid_i,
  input  logic [AXI_ADDR_WIDTH-1:0] axi_slave_ar_addr_i,
  input  logic [2:0]                axi_slave_ar_prot_i,
  input  logic [3:0]                axi_slave_ar_region_i,
  input  logic [7:0]                axi_slave_ar_len_i,
  input  logic [2:0]                axi_slave_ar_size_i,
  input  logic [1:0]                axi_slave_ar_burst_i,
  input  logic                      axi_slave_ar_lock_i,
  input  logic [3:0]                axi_slave_ar_cache_i,
  input  logic [3:0]                axi_slave_ar_qos_i,
  input  logic [AXI_ID_WIDTH-1:0]   axi_slave_ar_id_i,
  input  logic [AXI_USER_WIDTH-1:0] axi_slave_ar_user_i,
  output logic                      axi_slave_ar_ready_o,

  // WRITE DATA CHANNEL
  input  logic                      axi_slave_w_valid_i,
  input  logic [AXI_DATA_WIDTH-1:0] axi_slave_w_data_i,
  input  logic [AXI_STRB_WIDTH-1:0] axi_slave_w_strb_i,
  input  logic [AXI_USER_WIDTH-1:0] axi_slave_w_user_i,
  input  logic                      axi_slave_w_last_i,
  output logic                      axi_slave_w_ready_o,

  // PERIPHERAL REQUEST CHANNEL
  output logic                      per_master_req_o,
  output logic [PER_ADDR_WIDTH-1:0] per_master_add_o,
  output logic                      per_master_we_o,
  output logic [5:0]                per_master_atop_o,
  output logic [31:0]               per_master_wdata_o,
  output logic [3:0]                per_master_be_o,
  input  logic                      per_master_gnt_i,

  // CONTROL SIGNALS
  output logic                      trans_req_o,
  output logic                      trans_we_o,
  output logic                      trans_atop_r_o,
  output logic [AXI_ID_WIDTH-1:0]   trans_id_o,
  output logic [AXI_ADDR_WIDTH-1:0] trans_add_o,
  input  logic                      trans_r_valid_i,

  // BUSY SIGNAL
  output logic                      busy_o
);

  enum logic {TransIdle, TransPending} state_d, state_q;

  logic inv_wdata;

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= TransIdle;
    end else begin
      state_q <= state_d;
    end
  end

  // COMPUTE NEXT STATE
  always_comb begin
    axi_slave_aw_ready_o = 1'b0;
    axi_slave_ar_ready_o = 1'b0;
    axi_slave_w_ready_o  = 1'b0;

    per_master_req_o     = 1'b0;
    per_master_add_o     =   '0;
    per_master_we_o      = 1'b0;
    per_master_wdata_o   =   '0;
    per_master_be_o      =   '0;

    trans_req_o          = 1'b0;
    trans_id_o           =   '0;
    trans_add_o          =   '0;

    busy_o               = 1'b0;

    state_d              = state_q;

    case (state_q)
      TransIdle: begin
        // Handle request on AR
        if (axi_slave_ar_valid_i) begin
          per_master_req_o = 1'b1;
          per_master_we_o  = 1'b1; // write enable is active low
          per_master_add_o = axi_slave_ar_addr_i;

          if (per_master_gnt_i) begin
            axi_slave_ar_ready_o = 1'b1;

            trans_req_o          = 1'b1;
            trans_id_o           = axi_slave_ar_id_i;
            trans_add_o          = axi_slave_ar_addr_i;

            state_d              = TransPending;
          end
        // Handle request on AW and W
        end else if (axi_slave_aw_valid_i && axi_slave_w_valid_i) begin
          per_master_req_o = 1'b1;
          per_master_we_o  = 1'b0; // write enable is active low
          per_master_add_o = axi_slave_aw_addr_i;

          // Multiplex 64-bit W channel to 32-bit peripheral data channel based on the address.
          if (axi_slave_aw_addr_i[2]) begin
            per_master_be_o     = axi_slave_w_strb_i[7:4];
            per_master_wdata_o  = axi_slave_w_data_i[63:32];
          end else begin
            per_master_be_o     = axi_slave_w_strb_i[3:0];
            per_master_wdata_o  = axi_slave_w_data_i[31:0];
          end

          if (inv_wdata) begin
            per_master_wdata_o = ~per_master_wdata_o;
          end

          if (per_master_gnt_i) begin
            axi_slave_aw_ready_o = 1'b1;
            axi_slave_w_ready_o  = 1'b1;

            trans_req_o          = 1'b1;
            trans_id_o           = axi_slave_aw_id_i;
            trans_add_o          = axi_slave_aw_addr_i;

            state_d              = TransPending;
          end
        end
        per_master_add_o = per_master_add_o - (32'h0040_0000 * cluster_id_i);
      end

      TransPending: begin
        busy_o = 1'b1;
        if (trans_r_valid_i) begin
          // Received notification from response channel -> transaction completed.
          state_d = TransIdle;
        end
      end
    endcase
  end
  assign trans_we_o = per_master_we_o;

  always_comb begin
    inv_wdata = 1'b0;
    per_master_atop_o = '0;
    trans_atop_r_o = 1'b0;
    if (!per_master_we_o && axi_slave_aw_atop_i[5:4] != axi_pkg::ATOP_NONE) begin
      if (axi_slave_aw_atop_i == axi_pkg::ATOP_ATOMICSWAP) begin
        per_master_atop_o = riscv_defines::AMO_SWAP;
      end else begin
        case (axi_slave_aw_atop_i[2:0])
          axi_pkg::ATOP_ADD:  per_master_atop_o = riscv_defines::AMO_ADD;
          axi_pkg::ATOP_CLR: begin
            inv_wdata = 1'b1;
            per_master_atop_o = riscv_defines::AMO_AND;
          end
          axi_pkg::ATOP_EOR:  per_master_atop_o = riscv_defines::AMO_XOR;
          axi_pkg::ATOP_SET:  per_master_atop_o = riscv_defines::AMO_OR;
          axi_pkg::ATOP_SMAX: per_master_atop_o = riscv_defines::AMO_MAX;
          axi_pkg::ATOP_SMIN: per_master_atop_o = riscv_defines::AMO_MIN;
          axi_pkg::ATOP_UMAX: per_master_atop_o = riscv_defines::AMO_MAXU;
          axi_pkg::ATOP_UMIN: per_master_atop_o = riscv_defines::AMO_MINU;
        endcase
        if (axi_slave_aw_atop_i[5:4] == axi_pkg::ATOP_ATOMICLOAD) begin
          trans_atop_r_o = 1'b1;
        end
      end
    end
  end

  `ifndef TARGET_SYNTHESIS
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        axi_slave_aw_atop_i != axi_pkg::ATOP_ATOMICCMP)
      else $error("Atomic compare-and-swap not supported!");
  `endif

endmodule
