/// Copyright 2019 ETH Zurich
/// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
/// Author: Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
module snitch_serial_link #(
  parameter type axi_in_req_t   = snitch_axi_pkg::req_t,
  parameter type axi_in_resp_t  = snitch_axi_pkg::resp_t,
  parameter type axi_out_req_t  = snitch_axi_pkg::req_slv_t,
  parameter type axi_out_resp_t = snitch_axi_pkg::resp_slv_t
) (
  input logic            clk_i,
  input logic            rst_ni,
  input logic            testmode_i,

  input  axi_in_req_t    axi_in_req_i,
  output axi_in_resp_t   axi_in_resp_o,
  output axi_out_req_t   axi_out_req_o,
  input  axi_out_resp_t  axi_out_resp_i,

  // Physical IO
  input  logic       ddr_clk_i,
  input  logic [3:0] ddr_i,
  output logic [3:0] ddr_o
);

  logic ddr_rst_n;

  // TODO(zarubaf,fschuiki) ICEBOX: Fix
  // B beats are generated on the write site without the knowledge of the receiver.
  // Hence we also have no means to see whether writes actually succeeded.
  typedef enum logic [7:0]  {
    Idle  = 0,
    TagAW = 1,
    TagW = 2,
    TagAR  = 3,
    TagR  = 4
  } tag_e;

  typedef struct packed {
    tag_e tag;
    // logic [2:0] len;
    logic [63:0] data;
  } phy_payload_t;

  phy_payload_t phy_in_payload, phy_out_payload, phy_out_cdc_payload;
  logic phy_in_ready, phy_out_ready, phy_out_cdc_ready;
  logic phy_in_valid, phy_out_valid, phy_out_cdc_valid;

  // PHY Out FSM
  typedef enum logic {
    PHYIdle, PHYBusy
  } phy_state_e;

  phy_state_e phy_out_state_d, phy_out_state_q;
  phy_state_e phy_in_state_d, phy_in_state_q;
  logic [2:0] phy_out_index_d, phy_out_index_q;
  logic [2:0] phy_in_index_d, phy_in_index_q;
  logic [3:0] phy_out_credit_d, phy_out_credit_q;
  logic [3:0] credit_to_send_d, credit_to_send_q;
  logic       inc_phy_out_credit;
  logic       inc_credit_to_send;

  logic [$clog2(2)-1:0] mac_in_sel;

  logic [8:0] recv_fifo_empty;
  logic [8:0] recv_fifo_push;
  logic [8:0][7:0] recv_fifo_data_out;
  logic recv_fifo_pop;

  phy_payload_t mac_out_data, mac_in_data;
  logic         mac_out_valid, mac_out_ready, mac_in_valid, mac_in_ready;

  phy_payload_t mst_out_data, mst_in_data;
  logic         mst_out_valid, mst_out_ready, mst_in_valid, mst_in_ready;

  phy_payload_t slv_out_data, slv_in_data;
  logic         slv_out_valid, slv_out_ready, slv_in_valid, slv_in_ready;

  logic [7:0] data_in_q, data_out_q, data_out_d;
  logic [7:0] ddr_q, ddr_q2;

  // Protocol arbitration on out port
  stream_arbiter #(.DATA_T(phy_payload_t), .N_INP(2)) i_stream_arbiter (
    .clk_i       ( clk_i                          ),
    .rst_ni      ( rst_ni                         ),
    .inp_data_i  ( {mst_out_data,  slv_out_data}  ),
    .inp_valid_i ( {mst_out_valid, slv_out_valid} ),
    .inp_ready_o ( {mst_out_ready, slv_out_ready} ),
    .oup_data_o  ( mac_out_data                   ),
    .oup_valid_o ( mac_out_valid                  ),
    .oup_ready_i ( mac_out_ready                  )
  );

  stream_demux #(
    .N_OUP ( 2 )
  ) i_stream_demux (
    .inp_valid_i ( mac_in_valid ),
    .inp_ready_o ( mac_in_ready ),
    .oup_sel_i   ( mac_in_sel   ),
    .oup_valid_o ( {mst_in_valid, slv_in_valid} ),
    .oup_ready_i ( {mst_in_ready, slv_in_ready} )
  );

  assign mac_in_sel = mac_in_data.tag == TagR;
  assign mst_in_data = mac_in_data;
  assign slv_in_data = mac_in_data;

  // ------------------------
  // MAC (Clock: clk_i)
  // ------------------------
  // Master
  typedef enum logic [1:0] {
    MstIdle, MstRead, MstWrite, MstWriteAck
  } mst_state_e;

  mst_state_e mst_state_d, mst_state_q;

  logic [$bits(axi_in_req_i.aw.id)-1:0] mst_id_d, mst_id_q;
  logic [7:0] mst_len_d, mst_len_q;

  always_comb begin
    axi_in_resp_o = '0;
    mst_out_data = '0;
    mst_out_valid = '0;
    mst_in_ready = 1'b0;

    mst_id_d = mst_id_q;
    mst_state_d = mst_state_q;
    mst_len_d = mst_len_q;

    unique case (mst_state_q)
      MstIdle: begin
        if (axi_in_req_i.aw_valid) begin
          // write transaction
          mst_out_valid = 1'b1;
          mst_out_data.tag = TagAW;
          mst_out_data.data[31:0] = axi_in_req_i.aw.addr;
          mst_out_data.data[39:32] = axi_in_req_i.aw.len;
          mst_out_data.data[42:40] = axi_in_req_i.aw.size;
          axi_in_resp_o.aw_ready = mst_out_ready;
          mst_id_d = axi_in_req_i.aw.id;
          if (axi_in_resp_o.aw_ready) mst_state_d = MstWrite;
        end else if (axi_in_req_i.ar_valid) begin
          // read transaction
          mst_out_valid = 1'b1;
          mst_out_data.tag = TagAR;
          mst_out_data.data[31:0] = axi_in_req_i.ar.addr;
          mst_out_data.data[39:32] = axi_in_req_i.ar.len;
          mst_out_data.data[42:40] = axi_in_req_i.ar.size;
          mst_len_d = axi_in_req_i.ar.len;
          axi_in_resp_o.ar_ready = mst_out_ready;
          mst_id_d = axi_in_req_i.ar.id;
          if (axi_in_resp_o.ar_ready) mst_state_d = MstRead;
        end
      end

      MstWrite: begin
        if (axi_in_req_i.w_valid) begin
          mst_out_valid = 1'b1;
          mst_out_data.tag = TagW;
          mst_out_data.data = axi_in_req_i.w.data;
          axi_in_resp_o.w_ready = mst_out_ready;
          if (axi_in_resp_o.w_ready && axi_in_req_i.w.last) mst_state_d = MstWriteAck;
        end
      end

      MstWriteAck: begin
        axi_in_resp_o.b_valid = 1'b1;
        axi_in_resp_o.b.id = mst_id_q;
        if (axi_out_req_o.b_ready) mst_state_d = MstIdle;
      end

      MstRead: begin
        if (mst_in_valid) begin
          axi_in_resp_o.r_valid = 1'b1;
          axi_in_resp_o.r.data = mst_in_data;
          axi_in_resp_o.r.id = mst_id_q;
          axi_in_resp_o.r.last = (mst_len_q == 0);
          mst_in_ready = axi_in_req_i.r_ready;
          if (axi_in_req_i.r_ready) begin
            mst_len_d--;
            if (axi_in_resp_o.r.last) mst_state_d = MstIdle;
          end
        end
      end
      default : /* default */;
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mst_state_q <= MstIdle;
      mst_id_q <= '0;
      mst_len_q <= '0;
    end else begin
      mst_state_q <= mst_state_d;
      mst_id_q <= mst_id_d;
      mst_len_q <= mst_len_d;
    end
  end

  // Slave
  typedef enum logic [1:0] {
    SlvIdle, SlvRead, SlvWrite, SlvWriteAck
  } slv_state_e;

  slv_state_e slv_state_d, slv_state_q;
  logic [7:0] slv_len_d, slv_len_q;

  always_comb begin
    axi_out_req_o = '0;
    axi_out_req_o.b_ready = 1'b1;
    slv_len_d = slv_len_q;
    slv_state_d = slv_state_q;

    slv_out_data = '0;
    slv_out_valid = '0;
    slv_in_ready = 1'b0;

    unique case (slv_state_q)
      SlvIdle: begin
        if (slv_in_valid) begin
          if (slv_in_data.tag == TagAR) begin
            axi_out_req_o.ar_valid = 1'b1;
            axi_out_req_o.ar.addr = slv_in_data.data[31:0];
            axi_out_req_o.ar.len = slv_in_data.data[39:32];
            axi_out_req_o.ar.size = slv_in_data.data[42:40];
            slv_in_ready = axi_out_resp_i.ar_ready;
            slv_len_d = axi_out_req_o.ar.len;
            if (axi_out_resp_i.ar_ready && axi_out_req_o.ar_valid) slv_state_d = SlvRead;
          end else if (slv_in_data.tag == TagAW) begin
            axi_out_req_o.aw_valid = 1'b1;
            axi_out_req_o.aw.addr = slv_in_data.data[31:0];
            axi_out_req_o.aw.len = slv_in_data.data[39:32];
            axi_out_req_o.aw.size = slv_in_data.data[42:40];
            slv_in_ready = axi_out_resp_i.aw_ready;
            slv_len_d = axi_out_req_o.aw.len;
            if (axi_out_resp_i.aw_ready && axi_out_req_o.aw_valid) slv_state_d = SlvWrite;
          end
        end
      end

      SlvRead: begin
        if (axi_out_resp_i.r_valid) begin
          slv_out_data.tag = TagR;
          slv_out_data.data = axi_out_resp_i.r.data;
          axi_out_req_o.r_ready = slv_out_ready;
          slv_out_valid = 1'b1;
          if (axi_out_resp_i.r.last & axi_out_req_o.r_ready) slv_state_d = SlvIdle;
        end
      end

      SlvWrite: begin
        if (slv_in_valid) begin
          axi_out_req_o.w.data = slv_in_data.data;
          axi_out_req_o.w.strb = '1;
          axi_out_req_o.w_valid = 1'b1;
          slv_in_ready = axi_out_resp_i.w_ready;
          axi_out_req_o.w.last = (slv_len_q == 0);
          if (axi_out_resp_i.w_ready) begin
            slv_len_d--;
            if (slv_len_q == 0) slv_state_d = SlvIdle;
          end
        end
      end

      default : /* default */;
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      slv_state_q <= SlvIdle;
    end else begin
      slv_state_q <= slv_state_d;
    end
  end

  always_ff @(posedge clk_i) begin
    slv_len_q <= slv_len_d;
  end

  // ------------------------
  // PHY (Clock: ddr_clk_i)
  // ------------------------
  rstgen i_rstgen (.clk_i(ddr_clk_i), .rst_ni, .test_mode_i(testmode_i), .rst_no(ddr_rst_n), .init_no());

  cdc_2phase #(
    .T ( phy_payload_t )
  ) i_cdc_2phase_out (
    .src_clk_i   ( clk_i               ),
    .src_rst_ni  ( rst_ni              ),
    .src_data_i  ( mac_out_data        ),
    .src_valid_i ( mac_out_valid       ),
    .src_ready_o ( mac_out_ready       ),

    .dst_clk_i   ( ddr_clk_i           ),
    .dst_rst_ni  ( ddr_rst_n           ),
    .dst_data_o  ( phy_out_cdc_payload ),
    .dst_valid_o ( phy_out_cdc_valid   ),
    .dst_ready_i ( phy_out_cdc_ready   )
  );

  stream_register #(
    .T ( phy_payload_t )
  ) i_stream_reg_out (
      .clk_i   ( ddr_clk_i           ),
      .rst_ni  ( ddr_rst_n           ),
      .testmode_i,
      .clr_i   ( 1'b0                ),

      .data_i  ( phy_out_cdc_payload ),
      .valid_i ( phy_out_cdc_valid   ),
      .ready_o ( phy_out_cdc_ready   ),

      .data_o  ( phy_out_payload     ),
      .valid_o ( phy_out_valid       ),
      .ready_i ( phy_out_ready       )
  );


  cdc_2phase #(
    .T ( phy_payload_t )
  ) i_cdc_2phase_in (
    .src_clk_i   ( ddr_clk_i      ),
    .src_rst_ni  ( ddr_rst_n      ),
    .src_data_i  ( phy_in_payload ),
    .src_valid_i ( phy_in_valid   ),
    .src_ready_o ( phy_in_ready   ),

    .dst_clk_i   ( clk_i          ),
    .dst_rst_ni  ( rst_ni         ),
    .dst_data_o  ( mac_in_data    ),
    .dst_valid_o ( mac_in_valid   ),
    .dst_ready_i ( mac_in_ready   )
  );

  always_comb begin
    phy_out_ready = 1'b0;
    phy_out_state_d = phy_out_state_q;
    phy_out_index_d = phy_out_index_q;
    phy_out_credit_d = phy_out_credit_q;
    credit_to_send_d = credit_to_send_q;

    data_out_d = '0;

    unique case (phy_out_state_q)
      PHYIdle: begin
        if (phy_out_valid && phy_out_credit_q != '0) begin
          phy_out_state_d = PHYBusy;
          phy_out_index_d = '0;
          data_out_d = phy_out_payload.tag;
          phy_out_credit_d--;
        end
        if (credit_to_send_q != 0) begin
          data_out_d[7] = 1'b1;
          credit_to_send_d--;
        end
      end
      PHYBusy: begin
        phy_out_index_d = phy_out_index_q + 1;
        data_out_d = phy_out_payload.data >> (phy_out_index_q * 8);
        if (phy_out_index_q == 7) begin
          phy_out_state_d = PHYIdle;
          phy_out_ready = 1'b1;
        end
      end
      default : /* default */;
    endcase

    if (inc_phy_out_credit) phy_out_credit_d++;
    if (inc_credit_to_send) credit_to_send_d++;
  end
  // -------------
  // PHY In FSM
  // -------------
  always_comb begin
    phy_in_state_d = phy_in_state_q;
    phy_in_index_d = phy_in_index_q;
    inc_phy_out_credit = 1'b0;

    recv_fifo_push = '0;

    unique case (phy_in_state_q)
      PHYIdle: begin
        if (data_in_q[6:0] != 0) begin
          phy_in_state_d = PHYBusy;
          phy_in_index_d = '0;
          recv_fifo_push[8] = 1'b1;
        end
        // check whether we got a credit with MSB set
        if (data_in_q[7]) inc_phy_out_credit = 1'b1;
      end

      PHYBusy: begin
        phy_in_index_d++;
        recv_fifo_push = 1 << phy_in_index_q;
        if (phy_in_index_q == 7) phy_in_state_d = PHYIdle;
      end
      default : /* default */;
    endcase
  end

  for (genvar i = 0; i < 9; i++) begin : gen_recv_fifo
    logic [7:0] recv_fifo_data_in;

    fifo_v3 #(
      .FALL_THROUGH ( 1'b0 ),
      .DATA_WIDTH   ( 8    ),
      .DEPTH        ( 4    )
    ) i_fifo_v3 (
      .clk_i      ( ddr_clk_i                    ),
      .rst_ni     ( ddr_rst_n                    ),
      .flush_i    ( 1'b0                         ),
      .testmode_i ( testmode_i                   ),
      .full_o     (                              ),
      .empty_o    ( recv_fifo_empty[i]           ),
      .usage_o    (                              ),
      .data_i     ( recv_fifo_data_in            ),
      .push_i     ( recv_fifo_push[i]            ),
      .data_o     ( recv_fifo_data_out[i]        ),
      .pop_i      ( recv_fifo_pop                )
    );
    // clear upper bit which contains control flow
    assign recv_fifo_data_in = (i == 8) ? data_in_q & 8'h7F : data_in_q;
  end

  assign phy_in_valid = &(~recv_fifo_empty);
  assign recv_fifo_pop = phy_in_valid & phy_in_ready;
  assign inc_credit_to_send = recv_fifo_pop;
  assign phy_in_payload = phy_payload_t'(recv_fifo_data_out);

  always_ff @(posedge ddr_clk_i or negedge ddr_rst_n) begin
    if (!ddr_rst_n) begin
      phy_out_index_q <= '0;
      phy_in_index_q <= '0;
      phy_out_state_q <= PHYIdle;
      phy_in_state_q <= PHYIdle;
      phy_out_credit_q <= 3;
      credit_to_send_q <= 0;
    end else begin
      phy_out_index_q <= phy_out_index_d;
      phy_in_index_q <= phy_in_index_d;
      phy_out_state_q <= phy_out_state_d;
      phy_in_state_q <= phy_in_state_d;
      phy_out_credit_q <= phy_out_credit_d;
      credit_to_send_q <= credit_to_send_d;
    end
  end

  // DDR Out
  always_ff @(posedge ddr_clk_i, negedge rst_ni) data_out_q <= rst_ni ? data_out_d : '0;
  assign ddr_o = ddr_clk_i ? data_out_q[3:0] : data_out_q[7:4];

  // DDR In
  always_ff @(negedge ddr_clk_i, negedge rst_ni) ddr_q[3:0] <= rst_ni ? ddr_i : '0;
  always_ff @(posedge ddr_clk_i, negedge rst_ni) ddr_q[7:4] <= rst_ni ? ddr_i : '0;
  always_ff @(negedge ddr_clk_i, negedge rst_ni) ddr_q2 <= rst_ni ? ddr_q : '0;
  always_ff @(posedge ddr_clk_i, negedge rst_ni) data_in_q <= rst_ni ? ddr_q2 : '0;
endmodule

