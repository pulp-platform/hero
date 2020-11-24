`include "axi/assign.svh"

// Simulates a Baikonur environment. This fixture
// can be used for testing:
// - The governor which is essentially a single-core Snitch cluster
// - A `bowtruckle_cluster`: An 8 core Snitch cluster
// - Whole of `bowtruckle`: 3 `bowtruckle_cluster` + SoC

import "DPI-C" function read_elf(input string filename);
import "DPI-C" function byte get_section(output longint address, output longint len);
import "DPI-C" context function byte read_section(input longint address, inout byte buffer[]);
module fixture_baikonur #(
  parameter string DUT = "baikonur_governor" // "bowtruckle_cluster", "bowtruckle"
);
  localparam TCK = 1ns;
  localparam int unsigned CoreCount = 8;
  localparam BaikonurAddrWidth = 32;
  // The simulated memory.
  logic [63:0] memory[bit [31:0]];
  int sections [bit [31:0]];

  logic clk = 0;
  logic rst_ni;
  logic eoc = 0;

  logic rst, rst_n;
  assign rst = ~rst_ni;

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( BaikonurAddrWidth  ),
    .AXI_DATA_WIDTH ( snitch_axi_pkg::DataWidth  ),
    .AXI_ID_WIDTH   ( snitch_pkg::IdWidth        ),
    .AXI_USER_WIDTH ( snitch_axi_pkg::UserWidth  )
  ) master(clk);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( BaikonurAddrWidth ),
    .AXI_DATA_WIDTH ( snitch_axi_pkg::DataWidth ),
    .AXI_ID_WIDTH   ( snitch_pkg::IdWidthSlave  ),
    .AXI_USER_WIDTH ( snitch_axi_pkg::UserWidth )
  ) slave(clk);

  snitch_axi_pkg::req_t      axi_mst_req;
  snitch_axi_pkg::resp_t     axi_mst_resp;
  snitch_axi_pkg::req_slv_t  axi_slv_req;
  snitch_axi_pkg::resp_slv_t axi_slv_resp;

  if (DUT == "baikonur_governor") begin : gen_baikonur_governor
    baikonur_governor dut (
      .clk_i           ( clk              ),
      .rst_ni          ( rst_ni           ),
      .axi_mst_req_i   ( axi_mst_req      ),
      .axi_mst_resp_o  ( axi_mst_resp     ),
      .axi_slv_req_o   ( axi_slv_req      ),
      .axi_slv_resp_i  ( axi_slv_resp     )
    );
  end else if (DUT == "bowtruckle_cluster") begin : gen_bowtruckle_cluster
    logic rst;
    logic [9:0] cluster_id;
    assign rst = ~rst_ni;
    assign cluster_id = 0;
    bowtruckle_cluster dut (
      .clk_i           ( clk              ),
      .rst_i           ( rst              ),
      .cluster_id_i    ( cluster_id       ),
      .axi_mst_req_i   ( axi_mst_req      ),
      .axi_mst_resp_o  ( axi_mst_resp     ),
      .axi_slv_req_o   ( axi_slv_req      ),
      .axi_slv_resp_i  ( axi_slv_resp     )
    );
  end else if (DUT == "bowtruckle") begin : gen_bowtruckle
      bowtruckle dut (
      .clk_i           ( clk              ),
      .rst_ni          ( rst_ni           ),
      .testmode_i      ( 1'b0             ),
      .scan_enable_i   ( '0               ),
      .scan_data_i     ( '0               ),
      .scan_data_o     (                  ),
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
      .in_r_ready_i    ( master.r_ready   )
    );
  end

  if (DUT == "baikonur_governor" || DUT == "bowtruckle_cluster") begin
    // Cluster In
    `AXI_ASSIGN_TO_REQ(axi_mst_req, master)
    `AXI_ASSIGN_FROM_RESP(master, axi_mst_resp)
    // Cluster Out
    `AXI_ASSIGN_FROM_REQ(slave, axi_slv_req)
    `AXI_ASSIGN_TO_RESP(axi_slv_resp, slave)
  end

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

  initial begin
    memory[('h10010000 >> 3)] = 64'h00800593_f1402573; // csrr    a0,mhartid
                                                       // li      a1,8
    memory[('h10010008 >> 3)] = 64'h0f828293_00000297; // auipc   t0,0x0
                                                       // addi    t0,t0,248 # 10010100 <RAM>
    memory[('h10010010 >> 3)] = 64'h10500073_0002a283; // lw      t0,0(t0)
                                                       // wfi
    memory[('h10010018 >> 3)] = 64'h00000000_000282e7; // jalr    t0,t0
    // hack ahead
    // I have no idea why this is necessary for the bowtruckle netlist.
    // We've placed the exception pointer base to this address,
    // so in case we hit an exception lets just jump back to the bootloader.
    memory[('h30000000 >> 3)] = 64'h000080e7_e0010097; // auipc   ra,0xe0010
                                                       // jalr    ra
  end

  initial begin
    memory[('h1010_4000 >> 3)] = '0;
    // Bounce buffer
    memory[('h10010100 >> 3)] = 64'h80010000;
  end

  // Wait for reset to complete.
  task wait_for_reset;
    @(negedge rst_ni);
    @(posedge rst_ni);
    repeat (20) @(posedge clk);
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
      sections[section_addr>>3] = num_words;
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

  byte uart_buffer[$];

  // Handle the data output.
  typedef axi_test::axi_driver #(.AW(BaikonurAddrWidth), .DW(snitch_axi_pkg::DataWidth), .IW(snitch_pkg::IdWidthSlave), .UW(snitch_axi_pkg::UserWidth), .TA(0.1*TCK), .TT(0.9*TCK)) driver_out_t;
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
          ar_queue.pop_front();
        end
        driver_out.send_r(tx);
      end
      // W
      forever begin
        automatic driver_out_t::w_beat_t tx;
        automatic driver_out_t::ax_beat_t ax;
        automatic bit [31:0] word;
        driver_out.recv_w(tx);
        while (aw_queue.size() == 0) @aw_received;
        ax = aw_queue[0];
        word = ax.ax_addr >> 3;
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
          aw_queue.pop_front();
          b_queue.push_back(tx);
          -> b_ready;
        end
      end
      // B
      forever begin
        automatic driver_out_t::b_beat_t tx;
        while (b_queue.size() == 0) @b_ready;
        driver_out.send_b(b_queue[0]);
        b_queue.pop_front();
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
        uart_buffer.push_back(memory[32'hC0000000 >> 3][7:0]);
      end
    join_any
  end

  // Handle the data input.
  typedef axi_test::axi_driver #(.AW(BaikonurAddrWidth), .DW(snitch_axi_pkg::DataWidth), .IW(snitch_pkg::IdWidth), .UW(snitch_axi_pkg::UserWidth), .TA(0.1*TCK), .TT(0.9*TCK)) driver_in_t;
  driver_in_t driver_in = new(master);

  // Reset AXI.
  initial begin
    @(negedge rst_ni);
    driver_in.reset_master();
    @(posedge rst_ni);
  end

    // TODO(zarubaf): Break apart on 4k page boundary
    // TODO(zarubaf): Add error flags
    // Write `len` words beginning from `addr` taken from `data`.
    task automatic axi_write(input logic [31:0] addr, input int len, ref logic [63:0] data [$]);
      automatic driver_in_t::ax_beat_t ax = new();
      automatic driver_in_t::w_beat_t w = new();
      automatic driver_in_t::b_beat_t b;
      automatic int i;
      automatic int burst = 0;
      automatic int total_bursts = len / 256;
      assert(len <= $size(data)) else $error("Not enough data supplied to write");
      while (burst <= total_bursts) begin
        $display("%d/%d", burst, total_bursts);
        ax.ax_addr = addr + 256 * burst;
        ax.ax_id = '0;
        // check if we are at the las burst
        ax.ax_len = (burst != total_bursts) ? 255 : (len % 256) - 1;
        ax.ax_size = 3;
        driver_in.send_aw(ax);
        i = 0;
        do begin
          // $display("%h = %h", ax.ax_addr + i, data[i + 256 * burst]);
          w.w_data = data[i + 256 * burst];
          w.w_strb = '1;
          w.w_last = (i == ax.ax_len);
          driver_in.send_w(w);
          i++;
        end while (i <= ax.ax_len);
        driver_in.recv_b(b);
        burst++;
      end
    endtask

    // TODO(zarubaf): Break apart on 4k  page boundary
    // TODO(zarubaf): Add error flags
    // Read `len` words beginning from `addr` and store it in `data`.
    task automatic axi_read(input logic [31:0] addr, input int len, ref logic [63:0] data [$]);
        automatic driver_in_t::ax_beat_t ax = new();
        automatic driver_in_t::r_beat_t r;
        automatic int i = 0;
        @(posedge clk);
        ax.ax_addr = addr;
        ax.ax_id = $random();
        ax.ax_len = len - 1;
        ax.ax_size = 3;
        driver_in.send_ar(ax);
        do begin
            driver_in.recv_r(r);
            data.push_back(r.r_data);
            i++;
        end while (!r.r_last);
        assert(r.r_id == ax.ax_id);
    endtask
endmodule