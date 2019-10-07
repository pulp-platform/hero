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

module axi2per_res_channel #(
  // PARAMETERS
  parameter PER_ADDR_WIDTH = 32,
  parameter PER_ID_WIDTH   = 5,
  parameter AXI_ADDR_WIDTH = 32,
  parameter AXI_DATA_WIDTH = 64,
  parameter AXI_USER_WIDTH = 6,
  parameter AXI_ID_WIDTH   = 3
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  // PERIPHERAL INTERCONNECT MASTER
  //***************************************
  //RESPONSE CHANNEL
  input logic                       per_master_r_valid_i,
  input logic                       per_master_r_opc_i,
  input logic [31:0]                per_master_r_rdata_i,

  // AXI4 MASTER
  //***************************************
  // READ DATA CHANNEL
  output logic                      axi_slave_r_valid_o,
  output logic [AXI_DATA_WIDTH-1:0] axi_slave_r_data_o,
  output logic [1:0]                axi_slave_r_resp_o,
  output logic                      axi_slave_r_last_o,
  output logic [AXI_ID_WIDTH-1:0]   axi_slave_r_id_o,
  output logic [AXI_USER_WIDTH-1:0] axi_slave_r_user_o,
  input  logic                      axi_slave_r_ready_i,

  // WRITE RESPONSE CHANNEL
  output logic                      axi_slave_b_valid_o,
  output logic [1:0]                axi_slave_b_resp_o,
  output logic [AXI_ID_WIDTH-1:0]   axi_slave_b_id_o,
  output logic [AXI_USER_WIDTH-1:0] axi_slave_b_user_o,
  input  logic                      axi_slave_b_ready_i,

  // CONTROL SIGNALS
  input logic                       trans_req_i,
  input logic                       trans_we_i,
  input logic [AXI_ID_WIDTH-1:0]    trans_id_i,
  input logic [AXI_ADDR_WIDTH-1:0]  trans_add_i,
  output logic                      trans_r_valid_o
);

  logic [AXI_DATA_WIDTH-1:0]  s_axi_slave_r_data;

  logic [31:0]                s_per_master_r_data;

  logic                       s_trans_add_alignment,  //0 --> aligned to 64bit, 1--> not aligned to 64bit
                              s_trans_we_buf;
  logic [AXI_ID_WIDTH-1:0]    s_trans_id_buf;

  enum logic {TransIdle, TransPending} state_d, state_q;

  always_comb begin
    axi_slave_r_valid_o = 1'b0;
    axi_slave_r_data_o  =   '0;
    axi_slave_r_last_o  = 1'b0;

    axi_slave_b_valid_o = 1'b0;

    state_d             = state_q;

    unique case (state_q)
      TransIdle: begin
        if (per_master_r_valid_i) begin
          if ((s_trans_we_buf && axi_slave_r_ready_i) || // read and the R channel is ready
              (!s_trans_we_buf && axi_slave_b_ready_i)) begin // write and the B channel is ready
             state_d = TransPending;
          end
        end
      end

      TransPending: begin
        if (s_trans_we_buf && axi_slave_r_ready_i) begin // read and the R channel is ready
          axi_slave_r_valid_o = 1'b1;
          axi_slave_r_last_o  = 1'b1;
          axi_slave_r_data_o  = s_axi_slave_r_data;
          state_d = TransIdle;
        end else if (!trans_we_i && axi_slave_b_ready_i) begin // write and the B channel is ready
          axi_slave_b_valid_o = 1'b1;
          state_d = TransIdle;
        end
      end

      default: state_d = TransIdle;
    endcase
  end

  assign trans_r_valid_o = axi_slave_b_valid_o | axi_slave_r_valid_o;
  assign axi_slave_b_id_o = s_trans_id_buf;
  assign axi_slave_r_id_o = s_trans_id_buf;

  // Demultiplex the 32-bit data of the peripheral bus to the 64-bit AXI R channel.
  always_comb begin
    if (!s_trans_add_alignment) begin
      s_axi_slave_r_data = {32'b0, s_per_master_r_data};
    end else begin
      s_axi_slave_r_data = {s_per_master_r_data, 32'b0};
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      s_per_master_r_data   <=   '0;
      s_trans_add_alignment <= 1'b0;
      s_trans_id_buf        <=   '0;
      s_trans_we_buf        <= 1'b0;
      state_q               <= TransIdle;
    end else begin
      if (per_master_r_valid_i) begin
        s_per_master_r_data <= per_master_r_rdata_i;
      end
      if (trans_req_i) begin
        s_trans_add_alignment <= trans_add_i[2];
        s_trans_id_buf        <= trans_id_i;
        s_trans_we_buf        <= trans_we_i;
      end
      state_q <= state_d;
    end
  end

  // UNUSED SIGNALS
  assign axi_slave_r_resp_o = '0;
  assign axi_slave_r_user_o = '0;
  assign axi_slave_b_resp_o = '0;
  assign axi_slave_b_user_o = '0;

  `ifndef TARGET_SYNTHESIS
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        per_master_r_valid_i |-> state_q == TransIdle)
      else $error("Lost response on peripheral bus!");
  `endif

endmodule
