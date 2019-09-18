// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module axi4_r_sender
  #(
    parameter AXI_DATA_WIDTH = 32,
    parameter AXI_ID_WIDTH   = 4,
    parameter AXI_USER_WIDTH = 4
  )
  (
    input  logic                      axi4_aclk,
    input  logic                      axi4_arstn,

    input  logic                      drop_i,
    input  logic                [7:0] drop_len_i,
    output logic                      done_o,
    input  logic   [AXI_ID_WIDTH-1:0] id_i,
    input  logic                      prefetch_i,
    input  logic                      hit_i,

    output logic   [AXI_ID_WIDTH-1:0] s_axi4_rid,
    output logic                [1:0] s_axi4_rresp,
    output logic [AXI_DATA_WIDTH-1:0] s_axi4_rdata,
    output logic                      s_axi4_rlast,
    output logic                      s_axi4_rvalid,
    output logic [AXI_USER_WIDTH-1:0] s_axi4_ruser,
    input  logic                      s_axi4_rready,

    input  logic   [AXI_ID_WIDTH-1:0] m_axi4_rid,
    input  logic                [1:0] m_axi4_rresp,
    input  logic [AXI_DATA_WIDTH-1:0] m_axi4_rdata,
    input  logic                      m_axi4_rlast,
    input  logic                      m_axi4_rvalid,
    input  logic [AXI_USER_WIDTH-1:0] m_axi4_ruser,
    output logic                      m_axi4_rready
  );

  localparam BUFFER_DEPTH = 16;

  logic                    fifo_valid;
  logic                    fifo_pop;
  logic                    fifo_push;
  logic                    fifo_ready;
  logic [AXI_ID_WIDTH-1:0] id;
  logic              [7:0] len;
  logic                    prefetch;
  logic                    hit;

  logic                    dropping;

  enum logic [1:0]  { FORWARDING, DROPPING }
                            state_d,                state_q;
  logic                     burst_ongoing_d,        burst_ongoing_q;
  logic [7:0]               drop_cnt_d,             drop_cnt_q;

  axi_buffer_rab
    #(
      .DATA_WIDTH       ( 2+AXI_ID_WIDTH+8  ),
      .BUFFER_DEPTH     ( BUFFER_DEPTH      )
      )
    u_fifo
      (
        .clk       ( axi4_aclk                              ),
        .rstn      ( axi4_arstn                             ),
        // Pop
        .data_out  ( {prefetch,   hit,   id,   len}         ),
        .valid_out ( fifo_valid                             ),
        .ready_in  ( fifo_pop                               ),
        // Push
        .valid_in  ( fifo_push                              ),
        .data_in   ( {prefetch_i, hit_i, id_i, drop_len_i}  ),
        .ready_out ( fifo_ready                             )
      );

  assign fifo_push = drop_i & fifo_ready;
  assign done_o    = fifo_push;

  always_comb begin
    burst_ongoing_d = burst_ongoing_q;
    drop_cnt_d      = drop_cnt_q;
    dropping        = 1'b0;
    s_axi4_rlast    = 1'b0;
    fifo_pop        = 1'b0;
    state_d         = state_q;

    case (state_q)
      FORWARDING: begin
        s_axi4_rlast = m_axi4_rlast;
        // Remember whether there is currently a burst ongoing.
        if (m_axi4_rvalid && m_axi4_rready) begin
          if (m_axi4_rlast) begin
            burst_ongoing_d = 1'b0;
          end else begin
            burst_ongoing_d = 1'b1;
          end
        end
        // If there is no burst ongoing and the FIFO has a drop request ready, process it.
        if (!burst_ongoing_d && fifo_valid) begin
          drop_cnt_d  = len;
          state_d     = DROPPING;
        end
      end

      DROPPING: begin
        dropping      = 1'b1;
        s_axi4_rlast  = (drop_cnt_q == '0);
        // Handshake on slave interface
        if (s_axi4_rready) begin
          drop_cnt_d -= 1;
          if (drop_cnt_q == '0) begin
            drop_cnt_d  = '0;
            fifo_pop    = 1'b1;
            state_d     = FORWARDING;
          end
        end
      end

      default: begin
        state_d = FORWARDING;
      end
    endcase
  end

  assign s_axi4_rdata  = m_axi4_rdata;

  assign s_axi4_ruser  = dropping ? {AXI_USER_WIDTH{1'b0}} : m_axi4_ruser;
  assign s_axi4_rid    = dropping ? id : m_axi4_rid;

  assign s_axi4_rresp  = (dropping & prefetch & hit) ? 2'b00 : // prefetch hit, mutli, prot
                         (dropping & prefetch      ) ? 2'b10 : // prefetch miss
                         (dropping            & hit) ? 2'b10 : // non-prefetch multi, prot
                         (dropping                 ) ? 2'b10 : // non-prefetch miss
                         m_axi4_rresp;

  assign s_axi4_rvalid =  dropping | m_axi4_rvalid;
  assign m_axi4_rready = ~dropping & s_axi4_rready;

  always_ff @(posedge axi4_aclk, negedge axi4_arstn) begin
    if (axi4_arstn == 1'b0) begin
      burst_ongoing_q <= 1'b0;
      drop_cnt_q      <=  'b0;
      state_q         <= FORWARDING;
    end else begin
      burst_ongoing_q <= burst_ongoing_d;
      drop_cnt_q      <= drop_cnt_d;
      state_q         <= state_d;
    end
  end

endmodule


