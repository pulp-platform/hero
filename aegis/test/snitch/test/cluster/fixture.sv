module fixture;
  import "DPI-C" function read_elf(input string filename);
  import "DPI-C" function byte get_section(output longint address, output longint len);
  import "DPI-C" context function byte read_section(input longint address, inout byte buffer[]);

  localparam TCK = 1ns;
  localparam int unsigned CoreCount = 8;

  // The simulated memory.
  logic [63:0] memory[bit [60:0]];

  logic clk = 0;
  logic rst_ni;
  logic eoc = 0;

  logic rst, rst_n;
  assign rst = ~rst_ni;

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( snitch_axi_pkg::AddrWidth  ),
    .AXI_DATA_WIDTH ( snitch_axi_pkg::DataWidth  ),
    .AXI_ID_WIDTH   ( snitch_pkg::IdWidth        ),
    .AXI_USER_WIDTH ( snitch_axi_pkg::UserWidth  )
  ) master(clk);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( snitch_axi_pkg::AddrWidth ),
    .AXI_DATA_WIDTH ( snitch_axi_pkg::DataWidth ),
    .AXI_ID_WIDTH   ( snitch_pkg::IdWidthSlave  ),
    .AXI_USER_WIDTH ( snitch_axi_pkg::UserWidth )
  ) slave(clk);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( snitch_axi_pkg::DMAAddrWidth ),
    .AXI_DATA_WIDTH ( snitch_axi_pkg::DMADataWidth ),
    .AXI_ID_WIDTH   ( snitch_pkg::IdWidthDmaSlave  ),
    .AXI_USER_WIDTH ( snitch_axi_pkg::DMAUserWidth )
  ) dma(clk);

  snitch_cluster_synth_fixture dut (
    .clk_i           ( clk              ),
    .rst_i           ( rst              ),
    .out_aw_id_o     ( slave.aw_id      ),
    .out_aw_addr_o   ( slave.aw_addr    ),
    .out_aw_len_o    ( slave.aw_len     ),
    .out_aw_size_o   ( slave.aw_size    ),
    .out_aw_burst_o  ( slave.aw_burst   ),
    .out_aw_lock_o   ( slave.aw_lock    ),
    .out_aw_atop_o   ( slave.aw_atop    ),
    .out_aw_valid_o  ( slave.aw_valid   ),
    .out_aw_ready_i  ( slave.aw_ready   ),
    .out_w_data_o    ( slave.w_data     ),
    .out_w_strb_o    ( slave.w_strb     ),
    .out_w_last_o    ( slave.w_last     ),
    .out_w_valid_o   ( slave.w_valid    ),
    .out_w_ready_i   ( slave.w_ready    ),
    .out_b_id_i      ( slave.b_id       ),
    .out_b_resp_i    ( slave.b_resp     ),
    .out_b_valid_i   ( slave.b_valid    ),
    .out_b_ready_o   ( slave.b_ready    ),
    .out_ar_id_o     ( slave.ar_id      ),
    .out_ar_addr_o   ( slave.ar_addr    ),
    .out_ar_len_o    ( slave.ar_len     ),
    .out_ar_size_o   ( slave.ar_size    ),
    .out_ar_burst_o  ( slave.ar_burst   ),
    .out_ar_lock_o   ( slave.ar_lock    ),
    .out_ar_valid_o  ( slave.ar_valid   ),
    .out_ar_ready_i  ( slave.ar_ready   ),
    .out_r_id_i      ( slave.r_id       ),
    .out_r_data_i    ( slave.r_data     ),
    .out_r_resp_i    ( slave.r_resp     ),
    .out_r_last_i    ( slave.r_last     ),
    .out_r_valid_i   ( slave.r_valid    ),
    .out_r_ready_o   ( slave.r_ready    ),
    .in_aw_id_i      ( master.aw_id     ),
    .in_aw_addr_i    ( master.aw_addr   ),
    .in_aw_len_i     ( master.aw_len    ),
    .in_aw_size_i    ( master.aw_size   ),
    .in_aw_burst_i   ( master.aw_burst  ),
    .in_aw_lock_i    ( master.aw_lock   ),
    .in_aw_atop_i    ( master.aw_atop   ),
    .in_aw_valid_i   ( master.aw_valid  ),
    .in_aw_ready_o   ( master.aw_ready  ),
    .in_w_data_i     ( master.w_data    ),
    .in_w_strb_i     ( master.w_strb    ),
    .in_w_last_i     ( master.w_last    ),
    .in_w_valid_i    ( master.w_valid   ),
    .in_w_ready_o    ( master.w_ready   ),
    .in_b_id_o       ( master.b_id      ),
    .in_b_resp_o     ( master.b_resp    ),
    .in_b_valid_o    ( master.b_valid   ),
    .in_b_ready_i    ( master.b_ready   ),
    .in_ar_id_i      ( master.ar_id     ),
    .in_ar_addr_i    ( master.ar_addr   ),
    .in_ar_len_i     ( master.ar_len    ),
    .in_ar_size_i    ( master.ar_size   ),
    .in_ar_burst_i   ( master.ar_burst  ),
    .in_ar_lock_i    ( master.ar_lock   ),
    .in_ar_valid_i   ( master.ar_valid  ),
    .in_ar_ready_o   ( master.ar_ready  ),
    .in_r_id_o       ( master.r_id      ),
    .in_r_data_o     ( master.r_data    ),
    .in_r_resp_o     ( master.r_resp    ),
    .in_r_last_o     ( master.r_last    ),
    .in_r_valid_o    ( master.r_valid   ),
    .in_r_ready_i    ( master.r_ready   ),
    .dma_aw_id_o     ( dma.aw_id        ),
    .dma_aw_addr_o   ( dma.aw_addr      ),
    .dma_aw_len_o    ( dma.aw_len       ),
    .dma_aw_size_o   ( dma.aw_size      ),
    .dma_aw_burst_o  ( dma.aw_burst     ),
    .dma_aw_lock_o   ( dma.aw_lock      ),
    .dma_aw_atop_o   ( dma.aw_atop      ),
    .dma_aw_valid_o  ( dma.aw_valid     ),
    .dma_aw_ready_i  ( dma.aw_ready     ),
    .dma_w_data_o    ( dma.w_data       ),
    .dma_w_strb_o    ( dma.w_strb       ),
    .dma_w_last_o    ( dma.w_last       ),
    .dma_w_valid_o   ( dma.w_valid      ),
    .dma_w_ready_i   ( dma.w_ready      ),
    .dma_b_id_i      ( dma.b_id         ),
    .dma_b_resp_i    ( dma.b_resp       ),
    .dma_b_valid_i   ( dma.b_valid      ),
    .dma_b_ready_o   ( dma.b_ready      ),
    .dma_ar_id_o     ( dma.ar_id        ),
    .dma_ar_addr_o   ( dma.ar_addr      ),
    .dma_ar_len_o    ( dma.ar_len       ),
    .dma_ar_size_o   ( dma.ar_size      ),
    .dma_ar_burst_o  ( dma.ar_burst     ),
    .dma_ar_lock_o   ( dma.ar_lock      ),
    .dma_ar_valid_o  ( dma.ar_valid     ),
    .dma_ar_ready_i  ( dma.ar_ready     ),
    .dma_r_id_i      ( dma.r_id         ),
    .dma_r_data_i    ( dma.r_data       ),
    .dma_r_resp_i    ( dma.r_resp       ),
    .dma_r_last_i    ( dma.r_last       ),
    .dma_r_valid_i   ( dma.r_valid      ),
    .dma_r_ready_o   ( dma.r_ready      )
  );

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
      clk = 1;
      #(TCK/2);
      clk = 0;
      #(TCK/2);
    end
    repeat (8) begin
      clk = 1;
      #(TCK/2);
      clk = 0;
      #(TCK/2);
    end
  end

  // Wait for reset to complete.
  task wait_for_reset;
    @(negedge rst_ni);
    @(posedge rst_ni);
    @(posedge clk);
  endtask

  // Let the cluster run to completion.
  task run;
    @(posedge clk iff eoc == 1);
    $info("execution finished");
  endtask

  // Load an ELF binary.
  task load_binary;
    input string binary;
    longint section_addr, section_len;
    byte buffer[];
    void'(read_elf(binary));
    $display("Loading %s", binary);
    while (get_section(section_addr, section_len)) begin
      automatic int num_words = (section_len+7)/8;
      $display("Loading section %x", section_addr);
      buffer = new [num_words*8];
      void'(read_section(section_addr, buffer));
      for (int i = 0; i < num_words; i++) begin
        automatic logic [7:0][7:0] word = '0;
        for (int j = 0; j < 8; j++) begin
          word[j] = buffer[i*8+j];
        end
        memory[section_addr/8+i] = word;
      end
    end
  endtask

  // Handle the data input.
  typedef axi_test::axi_driver #(.AW(snitch_axi_pkg::AddrWidth), .DW(snitch_axi_pkg::DataWidth), .IW(snitch_pkg::IdWidth), .UW(snitch_axi_pkg::UserWidth), .TA(0.1*TCK), .TT(0.9*TCK)) driver_in_t;
  driver_in_t driver_in = new(master);
  initial begin
    automatic driver_in_t::ax_beat_t ax = new();
    automatic driver_in_t::w_beat_t w = new();
    automatic driver_in_t::b_beat_t b;
    @(negedge rst_ni);
    driver_in.reset_master();
    @(posedge rst_ni);
    @(posedge clk);
    ax.ax_addr = 'h0;
    ax.ax_id = '0;
    ax.ax_len = '0;
    ax.ax_size = 3;
    w.w_data = 64'h0;
    w.w_strb = '1;
    w.w_last = 1'b1;
    driver_in.send_aw(ax);
    driver_in.send_w(w);
    driver_in.recv_b(b);
  end

  byte uart_buffer[$];

  // Handle the data output.
  typedef axi_test::axi_driver #(.AW(snitch_axi_pkg::AddrWidth), .DW(snitch_axi_pkg::DataWidth), .IW(snitch_pkg::IdWidthSlave), .UW(snitch_axi_pkg::UserWidth), .TA(0.1*TCK), .TT(0.9*TCK)) driver_out_t;
  driver_out_t driver_out = new(slave);
  initial begin
    automatic driver_out_t::ax_beat_t aw_queue[$], ar_queue[$];
    automatic driver_out_t::b_beat_t b_queue[$];
    automatic string sb = "";

    event ar_received, aw_received, b_ready;
    event trigger_eoc;
    event char_received;

    @(negedge rst_ni);
    driver_out.reset_slave();
    @(posedge rst_ni);

    fork
      // AW
      forever begin
        automatic driver_out_t::ax_beat_t tx;
        driver_out.recv_aw(tx);
        aw_queue.push_back(tx);
        -> aw_received;
      end
      // AR
      forever begin
        automatic driver_out_t::ax_beat_t tx;
        driver_out.recv_ar(tx);
        ar_queue.push_back(tx);
        -> ar_received;
      end
      // R
      forever begin
        automatic driver_out_t::r_beat_t tx = new();
        automatic driver_out_t::ax_beat_t ax;
        automatic bit [63:0] word;
        while (ar_queue.size() == 0) @ar_received;
        ax = ar_queue[0];
        word = 64'b0;
        word[28:0] = ax.ax_addr >> 3;
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
        driver_out.send_r(tx);
      end
      // W
      forever begin
        automatic driver_out_t::w_beat_t tx;
        automatic driver_out_t::ax_beat_t ax;
        automatic bit [63:0] word;
        driver_out.recv_w(tx);
        while (aw_queue.size() == 0) @ar_received;
        ax = aw_queue[0];
        word = 64'b0;
        word[28:0] = ax.ax_addr >> 3;
        for (int i = 0; i < 8; i++) begin
          if (tx.w_strb[i]) begin
              memory[word][i*8+:8] = tx.w_data[i*8+:8];
          end
        end
        if (ax.ax_addr == 32'hD0000000) -> trigger_eoc;
        if (ax.ax_addr == 32'hC0000000) -> char_received;
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
        driver_out.send_b(b_queue[0]);
        void'(b_queue.pop_front());
      end
      // EOC
      forever begin
        @(trigger_eoc.triggered);
        eoc = 1;
        for (int i = 0; i < uart_buffer.size(); i++) begin
          sb = $sformatf("%s%c", sb, uart_buffer[i]);
        end
        $display("%s", sb);
      end
      // UART
      forever begin
        @char_received;
        uart_buffer.push_back(memory[64'hC0000000 >> 3][7:0]);
      end
    join_any
  end

  // Handle the data output from dma.
  typedef axi_test::axi_driver #(.AW(snitch_axi_pkg::DMAAddrWidth), .DW(snitch_axi_pkg::DMADataWidth), .IW(snitch_pkg::IdWidthDmaSlave), .UW(snitch_axi_pkg::DMAUserWidth), .TA(0.1*TCK), .TT(0.9*TCK)) driver_dma_t;
  driver_dma_t driver_dma = new(dma);
  initial begin
    automatic driver_dma_t::ax_beat_t aw_dma_queue[$], ar_dma_queue[$];
    automatic driver_dma_t::b_beat_t b_dma_queue[$];
    automatic string sb = "";

    event ar_dma_received, aw_dma_received, b_dma_ready;
    event trigger_dma_eoc;
    event char_dma_received;

    @(negedge rst_ni);
    driver_dma.reset_slave();
    @(posedge rst_ni);

    fork
      // AW
      forever begin
        automatic driver_dma_t::ax_beat_t dma_tx;
        driver_dma.recv_aw(dma_tx);
        aw_dma_queue.push_back(dma_tx);
        -> aw_dma_received;
      end
      // AR
      forever begin
        automatic driver_dma_t::ax_beat_t dma_tx;
        driver_dma.recv_ar(dma_tx);
        ar_dma_queue.push_back(dma_tx);
        -> ar_dma_received;
      end
      // R
      forever begin
        automatic driver_dma_t::r_beat_t dma_tx = new();
        automatic driver_dma_t::ax_beat_t dma_ax;
        automatic bit [63:0] word;
        automatic logic [511:0] mem_buffer;
        while (ar_dma_queue.size() == 0) @ar_dma_received;
        dma_ax = ar_dma_queue[0];
        // align address to bus
        word = (dma_ax.ax_addr >> 6) << 3;
        dma_tx.r_id = dma_ax.ax_id;
        for (int i = 0; i < 8; i++) begin
          mem_buffer[i*64+:64] = memory.exists(word + i) ? memory[word + i] : '0;
          // $display("loading buffer from %x with %x, buffer contains now: %x", word + i, memory[word + i], mem_buffer);
        end
        dma_tx.r_data = mem_buffer;
        // $display("DMA Read:  %x from %x", mem_buffer, word << 3);
        dma_tx.r_resp = axi_pkg::RESP_OKAY;
        dma_tx.r_last = (dma_ax.ax_len == 0);
        dma_ax.ax_addr >>= dma_ax.ax_size;
        dma_ax.ax_addr += 1;
        dma_ax.ax_addr <<= dma_ax.ax_size;
        dma_ax.ax_len -= 1;
        if (dma_tx.r_last) begin
          void'(ar_dma_queue.pop_front());
        end
        driver_dma.send_r(dma_tx);
      end
      // W
      forever begin
        automatic driver_dma_t::w_beat_t dma_tx;
        automatic driver_dma_t::ax_beat_t dma_ax;
        automatic bit [63:0] word;
        driver_dma.recv_w(dma_tx);
        while (aw_dma_queue.size() == 0) @ar_dma_received;
        dma_ax = aw_dma_queue[0];
        word = dma_ax.ax_addr >> 3;
        //$display("Ready to write");
        //$display("%x", word);
        for (int j = 0; j < 8; j++) begin
          for (int i = 0; i < 8; i++) begin
            if (dma_tx.w_strb[j*8+i]) begin
                memory[j+word][i*8+:8] = dma_tx.w_data[j*64+i*8+:8];
                //$display("%d - %d - %d", j, i, j*64+8*i);
                //$display("%x", dma_tx.w_data);
                //$display("%x", memory[j+word]);
            end
          end
        end
        // $display("DMA Write: %x to   %x", dma_tx.w_data, word << 3);
        if (dma_ax.ax_addr == 32'hD0000000) -> trigger_dma_eoc;
        if (dma_ax.ax_addr == 32'hC0000000) -> char_dma_received;
        dma_ax.ax_addr >>= dma_ax.ax_size;
        dma_ax.ax_addr += 1;
        dma_ax.ax_addr <<= dma_ax.ax_size;
        dma_ax.ax_len -= 1;
        if (dma_tx.w_last) begin
          automatic driver_dma_t::b_beat_t dma_tx = new();
          dma_tx.b_id = dma_ax.ax_id;
          dma_tx.b_user = dma_ax.ax_user;
          void'(aw_dma_queue.pop_front());
          b_dma_queue.push_back(dma_tx);
          -> b_dma_ready;
        end
      end
      // B
      forever begin
        automatic driver_dma_t::b_beat_t dma_tx;
        while (b_dma_queue.size() == 0) @b_dma_ready;
        driver_dma.send_b(b_dma_queue[0]);
        void'(b_dma_queue.pop_front());
      end
    join_any
  end


  // DMA output
  // AW
  initial begin
      forever begin
      @(posedge clk);
      #80ps;
          if (dma.aw_valid && dma.aw_ready) begin
              $display("%d: AW - id: %4d - addr: %x - len: %4d - size: %4d - burst: %b",
                       $time(),
                       dma.aw_id,
                       dma.aw_addr,
                       dma.aw_len,
                       dma.aw_size,
                       dma.aw_burst
                      );
          end
      end
  end

  // W
  initial begin
      forever begin
      @(posedge clk);
      #80ps;
          if (dma.w_valid && dma.w_ready) begin
              $display("%d:  W -            data: %x - strb: %x - last: %b",
                       $time(),
                       dma.w_data,
                       dma.w_strb,
                       dma.w_last
                      );
          end
      end
  end

  // AR
  initial begin
      forever begin
      @(posedge clk);
      #80ps;
          if (dma.ar_valid && dma.ar_ready) begin
              $display("%d: AR - id: %4d - addr: %x - len: %4d - size: %4d - burst: %b",
                       $time(),
                       dma.ar_id,
                       dma.ar_addr,
                       dma.ar_len,
                       dma.ar_size,
                       dma.ar_burst
                      );
          end
      end
  end

  // R
  initial begin
      forever begin
      @(posedge clk);
      #80ps;
          if (dma.r_ready && dma.r_valid) begin
              $display("%d:  R - id: %4d - data: %x - resp: %x                - last: %b",
                       $time(),
                       dma.r_id,
                       dma.r_data,
                       dma.r_resp,
                       dma.r_last
                      );
          end
      end
  end

endmodule
