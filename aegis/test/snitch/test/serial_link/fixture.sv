`include "axi/assign.svh"

module serial_fixture;
  localparam TCK = 1ns;
  localparam TCK_DDR = 5ns;

  logic clk_i;
  logic rst_ni;
  logic eoc = 1'b0;

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( snitch_axi_pkg::AddrWidth  ),
    .AXI_DATA_WIDTH ( snitch_axi_pkg::DataWidth  ),
    .AXI_ID_WIDTH   ( snitch_pkg::IdWidth        ),
    .AXI_USER_WIDTH ( snitch_axi_pkg::UserWidth  )
  ) alice_in (clk_i), bob_in(clk_i);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( snitch_axi_pkg::AddrWidth ),
    .AXI_DATA_WIDTH ( snitch_axi_pkg::DataWidth ),
    .AXI_ID_WIDTH   ( snitch_pkg::IdWidthSlave  ),
    .AXI_USER_WIDTH ( snitch_axi_pkg::UserWidth )
  ) alice_out(clk_i), bob_out(clk_i);

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( snitch_axi_pkg::AddrWidth  ),
    .AXI_DATA_WIDTH ( snitch_axi_pkg::DataWidth  ),
    .AXI_ID_WIDTH   ( snitch_pkg::IdWidth        ),
    .AXI_USER_WIDTH ( snitch_axi_pkg::UserWidth  )
  ) alice_in_dut (), bob_in_dut();

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( snitch_axi_pkg::AddrWidth ),
    .AXI_DATA_WIDTH ( snitch_axi_pkg::DataWidth ),
    .AXI_ID_WIDTH   ( snitch_pkg::IdWidthSlave  ),
    .AXI_USER_WIDTH ( snitch_axi_pkg::UserWidth )
  ) alice_out_dut(), bob_out_dut();

  snitch_axi_pkg::req_t alice_in_req;
  snitch_axi_pkg::resp_t alice_in_resp;
  snitch_axi_pkg::req_slv_t alice_out_req;
  snitch_axi_pkg::resp_slv_t alice_out_resp;

  snitch_axi_pkg::req_t bob_in_req;
  snitch_axi_pkg::resp_t bob_in_resp;
  snitch_axi_pkg::req_slv_t bob_out_req, bob_out_req_delayed;
  snitch_axi_pkg::resp_slv_t bob_out_resp, bob_out_resp_delayed;

  `AXI_ASSIGN_FROM_REQ(alice_out_dut, alice_out_req)
  `AXI_ASSIGN_TO_RESP(alice_out_resp, alice_out_dut)

  `AXI_ASSIGN_FROM_REQ(bob_out_dut, bob_out_req)
  `AXI_ASSIGN_TO_RESP(bob_out_resp, bob_out_dut)

  `AXI_ASSIGN_TO_REQ(alice_in_req, alice_in_dut)
  `AXI_ASSIGN_FROM_RESP(alice_in_dut, alice_in_resp)

  `AXI_ASSIGN_TO_REQ(bob_in_req, bob_in_dut)
  `AXI_ASSIGN_FROM_RESP(bob_in_dut, bob_in_resp)

  logic ddr_clk_i;
  logic [3:0] ddr_alice_out, ddr_bob_out;
  logic [3:0] ddr_alice_in, ddr_bob_in;

  snitch_serial_link alice (
    .clk_i          ( clk_i          ),
    .rst_ni         ( rst_ni         ),
    .testmode_i     ( 1'b0           ),
    .axi_in_req_i   ( alice_in_req   ),
    .axi_in_resp_o  ( alice_in_resp  ),
    .axi_out_req_o  ( alice_out_req  ),
    .axi_out_resp_i ( alice_out_resp ),
    .ddr_clk_i      ( ddr_clk_i      ),
    .ddr_i          ( ddr_alice_in   ),
    .ddr_o          ( ddr_alice_out  )
  );

  snitch_serial_link bob (
    .clk_i          ( clk_i                ),
    .rst_ni         ( rst_ni               ),
    .testmode_i     ( 1'b0                 ),
    .axi_in_req_i   ( bob_in_req           ),
    .axi_in_resp_o  ( bob_in_resp          ),
    .axi_out_req_o  ( bob_out_req_delayed  ),
    .axi_out_resp_i ( bob_out_resp_delayed ),
    .ddr_clk_i      ( ddr_clk_i            ),
    .ddr_i          ( ddr_bob_in           ),
    .ddr_o          ( ddr_bob_out          )
  );

  axi_delayer #(
    .aw_t             (snitch_axi_pkg::aw_chan_slv_t),
    .w_t              (snitch_axi_pkg::w_chan_t),
    .b_t              (snitch_axi_pkg::b_chan_slv_t),
    .ar_t             (snitch_axi_pkg::ar_chan_slv_t),
    .r_t              (snitch_axi_pkg::r_chan_slv_t),
    .StallRandomOutput(0),
    .StallRandomInput (0),
    .FixedDelayInput  (0),
    .FixedDelayOutput (0)
  ) i_axi_delayer (
    .clk_i      ( clk_i      ),
    .rst_ni     ( rst_ni     ),
    .aw_valid_i ( bob_out_req_delayed.aw_valid  ),
    .aw_chan_i  ( bob_out_req_delayed.aw        ),
    .aw_ready_o ( bob_out_resp_delayed.aw_ready ),
    .w_valid_i  ( bob_out_req_delayed.w_valid   ),
    .w_chan_i   ( bob_out_req_delayed.w         ),
    .w_ready_o  ( bob_out_resp_delayed.w_ready  ),
    .b_valid_o  ( bob_out_resp_delayed.b_valid  ),
    .b_chan_o   ( bob_out_resp_delayed.b   ),
    .b_ready_i  ( bob_out_req_delayed.b_ready  ),
    .ar_valid_i ( bob_out_req_delayed.ar_valid ),
    .ar_chan_i  ( bob_out_req_delayed.ar  ),
    .ar_ready_o ( bob_out_resp_delayed.ar_ready ),
    .r_valid_o  ( bob_out_resp_delayed.r_valid  ),
    .r_chan_o   ( bob_out_resp_delayed.r   ),
    .r_ready_i  ( bob_out_req_delayed.r_ready  ),

    .aw_valid_o ( bob_out_req.aw_valid ),
    .aw_chan_o  ( bob_out_req.aw  ),
    .aw_ready_i ( bob_out_resp.aw_ready ),
    .w_valid_o  ( bob_out_req.w_valid  ),
    .w_chan_o   ( bob_out_req.w   ),
    .w_ready_i  ( bob_out_resp.w_ready  ),
    .b_valid_i  ( bob_out_resp.b_valid  ),
    .b_chan_i   ( bob_out_resp.b   ),
    .b_ready_o  ( bob_out_req.b_ready  ),
    .ar_valid_o ( bob_out_req.ar_valid ),
    .ar_chan_o  ( bob_out_req.ar  ),
    .ar_ready_i ( bob_out_resp.ar_ready ),
    .r_valid_i  ( bob_out_resp.r_valid  ),
    .r_chan_i   ( bob_out_resp.r   ),
    .r_ready_o  ( bob_out_req.r_ready  )
  );

  assign #(0.25*TCK_DDR) ddr_bob_in = ddr_alice_out;
  assign #(0.25*TCK_DDR) ddr_alice_in = ddr_bob_out;

  typedef axi_test::axi_driver #(.AW(snitch_axi_pkg::AddrWidth), .DW(snitch_axi_pkg::DataWidth), .IW(snitch_pkg::IdWidth), .UW(snitch_axi_pkg::UserWidth), .TA(0.1*TCK), .TT(0.9*TCK)) driver_in_t;
  typedef axi_test::axi_driver #(.AW(snitch_axi_pkg::AddrWidth), .DW(snitch_axi_pkg::DataWidth), .IW(snitch_pkg::IdWidthSlave), .UW(snitch_axi_pkg::UserWidth), .TA(0.1*TCK), .TT(0.9*TCK)) driver_out_t;

  logic [63:0] memory[bit [31:0]];

  task wait_for_reset;
    @(negedge rst_ni);
    @(posedge rst_ni);
    repeat (5) @(posedge clk_i);
    repeat (5) @(posedge ddr_clk_i);
  endtask

  task finish;
    @(posedge clk_i);
    eoc = 1;
  endtask

  task write (driver_in_t drv_in, logic [31:0] addr, logic [63:0] data [$]);
    automatic driver_in_t::ax_beat_t ax = new();
    automatic driver_in_t::w_beat_t w = new();
    automatic driver_in_t::b_beat_t b;
    automatic int i;
    ax.ax_addr = addr;
    ax.ax_id = '0;
    ax.ax_len = data.size() - 1;
    ax.ax_size = 3;
    drv_in.send_aw(ax);
    i = 0;
    do begin
      w.w_data = data[i];
      w.w_strb = '1;
      w.w_last = (ax.ax_len == i);
      drv_in.send_w(w);
      i++;
    end while (i <= ax.ax_len);
    drv_in.recv_b(b);
  endtask

  task read (driver_in_t drv_in, logic [31:0] addr, logic [7:0] len, logic [63:0] data [$]);
    automatic driver_in_t::ax_beat_t ax = new();
    automatic driver_in_t::r_beat_t r;
    ax.ax_addr = addr;
    ax.ax_id = '0;
    ax.ax_len = len - 1;
    ax.ax_size = 3;
    drv_in.send_ar(ax);
    do begin
      drv_in.recv_r(r);
      data.push_back(r.r_data);
    end while (!r.r_last);
  endtask

  initial begin
    rst_ni = 1;
    #10ns;
    rst_ni = 0;
    #10ns;
    rst_ni = 1;
  end
  // Generate reset and clock.
  initial begin
    while (!eoc) begin
      clk_i = 1;
      #(TCK/2);
      clk_i = 0;
      #(TCK/2);
    end
    repeat (8) begin
      clk_i = 1;
      #(TCK/2);
      clk_i = 0;
      #(TCK/2);
    end
  end

  // Generate reset and clock.
  initial begin
    while (!eoc) begin
      ddr_clk_i = 1;
      #(TCK_DDR/2);
      ddr_clk_i = 0;
      #(TCK_DDR/2);
    end
    repeat (8) begin
      ddr_clk_i = 1;
      #(TCK_DDR/2);
      ddr_clk_i = 0;
      #(TCK_DDR/2);
    end
  end

  `AXI_ASSIGN(alice_in_dut, alice_in)
  `AXI_ASSIGN(bob_in_dut, bob_in)
  `AXI_ASSIGN(alice_out, alice_out_dut)
  `AXI_ASSIGN(bob_out, bob_out_dut)

  driver_in_t alice_driver_in = new(alice_in);
  driver_in_t bob_driver_in = new(bob_in);

  driver_out_t alice_driver_out = new(alice_out);
  driver_out_t bob_driver_out = new(bob_out);

  // Alice Slave
  initial begin
    automatic driver_out_t::ax_beat_t aw_queue[$], ar_queue[$];
    automatic driver_out_t::b_beat_t b_queue[$];
    automatic string sb = "";

    event ar_received, aw_received, b_ready;

    @(negedge rst_ni);
    alice_driver_out.reset_slave();
    @(posedge rst_ni);

    fork
      // AW
      forever begin
        automatic driver_out_t::ax_beat_t tx;
        alice_driver_out.recv_aw(tx);
        aw_queue.push_back(tx);
        -> aw_received;
      end
      // AR
      forever begin
        automatic driver_out_t::ax_beat_t tx;
        alice_driver_out.recv_ar(tx);
        ar_queue.push_back(tx);
        -> ar_received;
      end
      // R
      forever begin
        automatic driver_out_t::r_beat_t tx = new();
        automatic driver_out_t::ax_beat_t ax;
        automatic bit [31:0] word;
        while (ar_queue.size() == 0) @ar_received;
        ax = ar_queue[0];
        word = ax.ax_addr >> 3;
        tx.r_id = ax.ax_id;
        tx.r_data = memory.exists(word) ? memory[word] : '0;
        tx.r_resp = axi_pkg::RESP_OKAY;
        tx.r_last = (ax.ax_len == 0);
        ax.ax_addr >>= ax.ax_size;
        ax.ax_addr += 1;
        ax.ax_addr <<= ax.ax_size;
        ax.ax_len -= 1;
        if (tx.r_last) begin
          void'(ar_queue.pop_front());
        end
        alice_driver_out.send_r(tx);
      end
      // W
      forever begin
        automatic driver_out_t::w_beat_t tx;
        automatic driver_out_t::ax_beat_t ax;
        automatic bit [31:0] word;
        alice_driver_out.recv_w(tx);
        while (aw_queue.size() == 0) @ar_received;
        ax = aw_queue[0];
        word = ax.ax_addr >> 3;
        for (int i = 0; i < 8; i++) begin
          if (tx.w_strb[i]) begin
              memory[word][i*8+:8] = tx.w_data[i*8+:8];
          end
        end
        ax.ax_addr >>= ax.ax_size;
        ax.ax_addr += 1;
        ax.ax_addr <<= ax.ax_size;
        ax.ax_len -= 1;
        if (tx.w_last) begin
          automatic driver_out_t::b_beat_t tx = new();
          tx.b_id = ax.ax_id;
          tx.b_user = ax.ax_user;
          void'(aw_queue.pop_front());
          b_queue.push_back(tx);
          -> b_ready;
        end
      end
      // B
      forever begin
        automatic driver_out_t::b_beat_t tx;
        while (b_queue.size() == 0) @b_ready;
        alice_driver_out.send_b(b_queue[0]);
        void'(b_queue.pop_front());
      end
    join_any
  end

  // Bob Slave
  initial begin
    automatic driver_out_t::ax_beat_t aw_queue[$], ar_queue[$];
    automatic driver_out_t::b_beat_t b_queue[$];
    automatic string sb = "";

    event ar_received, aw_received, b_ready;

    @(negedge rst_ni);
    bob_driver_out.reset_slave();
    @(posedge rst_ni);

    fork
      // AW
      forever begin
        automatic driver_out_t::ax_beat_t tx;
        bob_driver_out.recv_aw(tx);
        aw_queue.push_back(tx);
        -> aw_received;
      end
      // AR
      forever begin
        automatic driver_out_t::ax_beat_t tx;
        bob_driver_out.recv_ar(tx);
        ar_queue.push_back(tx);
        -> ar_received;
      end
      // R
      forever begin
        automatic driver_out_t::r_beat_t tx = new();
        automatic driver_out_t::ax_beat_t ax;
        automatic bit [31:0] word;
        while (ar_queue.size() == 0) @ar_received;
        ax = ar_queue[0];
        word = ax.ax_addr >> 3;
        tx.r_id = ax.ax_id;
        tx.r_data = memory.exists(word) ? memory[word] : '0;
        tx.r_resp = axi_pkg::RESP_OKAY;
        tx.r_last = (ax.ax_len == 0);
        ax.ax_addr >>= ax.ax_size;
        ax.ax_addr += 1;
        ax.ax_addr <<= ax.ax_size;
        ax.ax_len -= 1;
        if (tx.r_last) begin
          void'(ar_queue.pop_front());
        end
        bob_driver_out.send_r(tx);
      end
      // W
      forever begin
        automatic driver_out_t::w_beat_t tx;
        automatic driver_out_t::ax_beat_t ax;
        automatic bit [31:0] word;
        // repeat (1000) @(posedge clk_i);
        bob_driver_out.recv_w(tx);
        while (aw_queue.size() == 0) @ar_received;
        ax = aw_queue[0];
        word = ax.ax_addr >> 3;
        for (int i = 0; i < 8; i++) begin
          if (tx.w_strb[i]) begin
              memory[word][i*8+:8] = tx.w_data[i*8+:8];
          end
        end
        ax.ax_addr >>= ax.ax_size;
        ax.ax_addr += 1;
        ax.ax_addr <<= ax.ax_size;
        ax.ax_len -= 1;
        if (tx.w_last) begin
          automatic driver_out_t::b_beat_t tx = new();
          tx.b_id = ax.ax_id;
          tx.b_user = ax.ax_user;
          void'(aw_queue.pop_front());
          b_queue.push_back(tx);
          -> b_ready;
        end
      end
      // B
      forever begin
        automatic driver_out_t::b_beat_t tx;
        while (b_queue.size() == 0) @b_ready;
        bob_driver_out.send_b(b_queue[0]);
        void'(b_queue.pop_front());
      end
    join_any
  end
endmodule
