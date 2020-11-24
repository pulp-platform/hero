
`include "axi/assign.svh"

module fixture_frankensnitch_cc;
  import "DPI-C" function read_elf(input string filename);
  import "DPI-C" function byte get_section(output longint address, output longint len);
  import "DPI-C" context function byte read_section(input longint address, inout byte buffer[]);

  import snitch_pkg::*;
  import reqrsp_test::*;

  localparam TCK  = 1ns;
  localparam TA   = 0.2ns;  // must be nonzero to avoid Snitch load fifo double pop glitch
  localparam TT   = 0.8ns;

  // Addresses
  localparam logic [31:0] BootAddr      = 32'h8001_0000;
  localparam logic [31:0] UartAddr      = 32'hC000_0000;
  localparam logic [31:0] EocAddr       = 32'hD000_0000;
  localparam logic [31:0] TcdmStartAddr = 32'h4000_0000;
  localparam logic [31:0] TcdmEndAddr   = 32'h4000_0008;
  localparam logic [31:0] NrCoresAddr   = 32'h4000_0010;

  logic rst, rst_n, axi_rst_n;
  logic clk     = 1'b0;
  logic running = 1'b0;
  logic eoc     = 1'b0;
  assign rst_n = ~rst;

  // -------------------- DUT --------------------

  // DUT Signals
  logic [31:0]      inst_addr_o;
  logic [31:0]      inst_data_i;
  logic             inst_valid_o;
  logic             inst_ready_i;

  acc_req_t         acc_req_o;
  logic             acc_qvalid_o;
  logic             acc_qready_i;
  acc_resp_t        acc_resp_i;
  logic             acc_pvalid_i;
  logic             acc_pready_o;

  core_events_t     core_events_o;

  logic             wake_up_sync_i = 1'b0;

  // DMA signals
  axi_dma_pkg::req_t axi_dma_req;
  axi_dma_pkg::res_t axi_dma_res;
  logic              axi_dma_busy;

  REQRSP_BUS #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(64),
    .ID_WIDTH(1)
  ) dbus [2] (clk);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( 64  ),
    .AXI_DATA_WIDTH ( 512 ),
    .AXI_ID_WIDTH   ( 4   ),
    .AXI_USER_WIDTH ( 1   )
  ) dma (clk);

  `AXI_ASSIGN_FROM_REQ(dma, axi_dma_req)
  `AXI_ASSIGN_TO_RESP(axi_dma_res, dma)

  // DUT
  snitch_cc #(
    .BootAddr       ( BootAddr            ),
    .SDMA           ( 1                   ),
    .RVFD           ( 0                   ),
    .FPUSequencer   ( 0                   ),
    .axi_dma_req_t  ( axi_dma_pkg::req_t  ),
    .axi_dma_res_t  ( axi_dma_pkg::res_t  )
  ) dut (
    .clk_i          ( clk             ),
    .rst_i          ( rst             ),
    .hart_id_i      ( 'h10000         ),
    // IMEM Port
    .inst_addr_o    ( inst_addr_o     ),
    .inst_data_i    ( inst_data_i     ),
    .inst_valid_o   ( inst_valid_o    ),
    .inst_ready_i   ( inst_ready_i    ),
    // Data Ports
    .data_qaddr_o   ( {dbus[1].qaddr,   dbus[0].qaddr}  ),
    .data_qwrite_o  ( {dbus[1].qwrite,  dbus[0].qwrite} ),
    .data_qamo_o    (  ),
    .data_qdata_o   ( {dbus[1].qdata,   dbus[0].qdata}  ),
    .data_qstrb_o   ( {dbus[1].qstrb,   dbus[0].qstrb}  ),
    .data_qvalid_o  ( {dbus[1].qvalid,  dbus[0].qvalid} ),
    .data_qready_i  ( {dbus[1].qready,  dbus[0].qready} ),
    .data_pdata_i   ( {dbus[1].pdata,   dbus[0].pdata}  ),
    .data_perror_i  ( {dbus[1].perror,  dbus[0].perror} ),
    .data_pvalid_i  ( {dbus[1].pvalid,  dbus[0].pvalid} ),
    .data_pready_o  ( {dbus[1].pready,  dbus[0].pready} ),
    .wake_up_sync_i ( wake_up_sync_i  ),
    // Accelerator Port
    .acc_req_o      ( acc_req_o       ),
    .acc_qvalid_o   ( acc_qvalid_o    ),
    .acc_qready_i   ( acc_qready_i    ),
    .acc_resp_i     ( acc_resp_i      ),
    .acc_pvalid_i   ( acc_pvalid_i    ),
    .acc_pready_o   ( acc_pready_o    ),
    // DMA interface
    .axi_dma_req_o  ( axi_dma_req     ),
    .axi_dma_res_i  ( axi_dma_res     ),
    .axi_dma_busy_o ( axi_dma_busy    ),
    // Core Events
    .core_events_o  ( core_events_o   )
  );

  // -------------------- DMA Mem Sys --------------------
  /*axi_dma_observer #(
      .ADDR_WIDTH  ( 64         ),
      .DATA_WIDTH  ( 512        )
  ) i_observer (
      .clk_i         ( clk          ),
      .rst_ni        ( rst_n        ),
      .axi_dma_req_i ( axi_dma_req  ),
      .axi_dma_res_o ( axi_dma_res  )
  );*/

  // lfsr
  logic [784:0] lfsr_d;
  logic [784:0] lfsr_q = 'hc0a232c162b2bab5b960668030f4efce27940bd0de965f0b8d4315f15b79704195e4e0a6b495fc269f65ae17e10e9ca98510fc143327a292b418597f9dd175fc91c3d61be287d5462a23e00fa7ae906ae9eb339ab5225021356138cd46b6e5a73540c5591116b6b5e08d2c0e54eaf0d5143b33b2186b6cf841c076a98c412a63981f0e323dce93481ed1c37e4f1d7553b6c2fba1a3af6c3ad88b15ad58812ba07d1753917ac4e6ab1e8c4f67a47b4b0f48a34f42a52c546e979f4e4968e80a732a0a5e7a51146cf08482f349f94336752b765c0b1d70803d883d5058d127264335213da4163c62f65a4e65501b90fa5f177675c0747cfca328e131bfb3f7bcc5c27680c7bf86491f4ed3d36c25531edfa74b1e32fafe426958ae356eb8ef0fd818eaca4227a667b7c934ebfa282ab6bfc6db89b927c91a41e63a9554dced774f30268d0725a1a565368703b9f81d5c027ba196ef8b803a51c639c7ead834e1d6bc537d33800fe5eb12f1ed67758f1dfe85ffdbae56e8ef27f2ecedcee75b8dbb5f5f1a629ba3b755;

  logic lfsr_ena;
  // bulk shift
  always_comb begin : proc_lfsr
    for (int i = 1; i < 785; i = i +1) lfsr_d[i-1] = lfsr_q[i];
    lfsr_d[784] = lfsr_q[0];
    lfsr_d[692] = lfsr_q[0] ^ lfsr_q[693];
  end

  // Memory
  logic [63:0] dma_memory [bit [60:0]];

  // Handle the data output from dma.
  typedef axi_test::axi_driver #(.AW(64), .DW(512), .IW(4), .UW(1), .TA(0.1*TCK), .TT(0.9*TCK)) driver_dma_t;
  driver_dma_t driver_dma = new(dma);
  initial begin
    automatic driver_dma_t::ax_beat_t aw_dma_queue[$], ar_dma_queue[$];
    automatic driver_dma_t::b_beat_t b_dma_queue[$];
    automatic string sb = "";

    event ar_dma_received, aw_dma_received, b_dma_ready;
    event lfsr_read;

    @(posedge rst);
    driver_dma.reset_slave();
    @(negedge rst);

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
        word = dma_ax.ax_addr >> 3;
        dma_tx.r_id = dma_ax.ax_id;
        for (int i = 0; i < 8; i++) begin
          if (!dma_memory.exists(word + i)) begin
            dma_memory[word + i] = lfsr_q[i*64+:64];
            -> lfsr_read;
          end
          mem_buffer[i*64+:64]   = dma_memory[word + i];
          // $display("loading buffer from %x with %x, buffer contains now: %x", word + i, dma_memory[word + i], mem_buffer);
        end

        dma_tx.r_data = mem_buffer;
        // $display("%d - DMA Read:            %x - from: %x", $time, mem_buffer, word << 3);
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
                dma_memory[j+word][i*8+:8] = dma_tx.w_data[j*64+i*8+:8];
                //$display("%d - %d - %d", j, i, j*64+8*i);
                //$display("%x", dma_tx.w_data);
                //$display("%x", dma_memory[j+word]);
            end
          end
        end
        // $display("%d - DMA Write:           %x - to:   %x", $time, dma_tx.w_data, word << 3);
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
      // next lfsr
      forever begin
        @(lfsr_read.triggered)
        lfsr_q <= lfsr_d;
      end
    join_any
  end

  // AW
  initial begin
      forever begin
      @(posedge clk);
      #80ps;
          if (axi_dma_req.aw_valid && axi_dma_res.aw_ready) begin
              $display("%d: AW - id: %4d - addr: %x - len: %4d - size: %4d - burst: %b",
                       $time(),
                       axi_dma_req.aw.id,
                       axi_dma_req.aw.addr,
                       axi_dma_req.aw.len,
                       axi_dma_req.aw.size,
                       axi_dma_req.aw.burst
                      );
          end
      end
  end

  // W
  initial begin
      forever begin
      @(posedge clk);
      #80ps;
          if (axi_dma_req.w_valid && axi_dma_res.w_ready) begin
              $display("%d:  W -            data: %x - strb: %x - last: %b",
                       $time(),
                       axi_dma_req.w.data,
                       axi_dma_req.w.strb,
                       axi_dma_req.w.last
                      );
          end
      end
  end

  // AR
  initial begin
      forever begin
      @(posedge clk);
      #80ps;
          if (axi_dma_req.ar_valid && axi_dma_res.ar_ready) begin
              $display("%d: AR - id: %4d - addr: %x - len: %4d - size: %4d - burst: %b",
                       $time(),
                       axi_dma_req.ar.id,
                       axi_dma_req.ar.addr,
                       axi_dma_req.ar.len,
                       axi_dma_req.ar.size,
                       axi_dma_req.ar.burst
                      );
          end
      end
  end

  // R
  initial begin
      forever begin
      @(posedge clk);
      #80ps;
          if (axi_dma_req.r_ready && axi_dma_res.r_valid) begin
              $display("%d:  R - id: %4d - data: %x - resp: %x                - last: %b",
                       $time(),
                       axi_dma_res.r.id,
                       axi_dma_res.r.data,
                       axi_dma_res.r.resp,
                       axi_dma_res.r.last
                      );
          end
      end
  end

  // -------------------- Memory System --------------------

  // Memory
  logic [63:0] memory [bit [28:0]];

  // Initialize peripheral registers
  initial begin
    memory[BootAddr       >> 3] = 64'h0;
    memory[TcdmStartAddr  >> 3] = 64'h0;
    memory[TcdmEndAddr    >> 3] = 64'h0;
    memory[NrCoresAddr    >> 3] = 64'h8;
  end

  // Return code
  logic [31:0] exit_code = 'X;

  // IMEM read port
  assign inst_ready_i = running;
  assign inst_data_i  = (running ? memory[inst_addr_o >> 3][(inst_addr_o[2] ? 32 : 0) +: 32]: 32'hx);

  // UART
  event   evt_uart_char;
  always @evt_uart_char begin
    uart_buffer.push_back(memory[UartAddr >> 3][7:0]);
  end

  // EOC
  event   evt_eoc;
  byte    uart_buffer [$];
  string  sb = "";
  always @evt_eoc begin
    eoc       = 1'b1;
    running   = 1'b0;
    exit_code = memory[EocAddr >> 3][31:0];
    for (int i = 0; i < uart_buffer.size(); i++) begin
      sb = $sformatf("%s%c", sb, uart_buffer[i]);
    end
    $display("%s", sb);
  end

  //DMEM reqrsp ports
  for (genvar i = 0; i < 2; i++) begin : gen_dmem_ports
    event   resp_ready;
    mailbox resp_queue = new();
    reqrsp_driver #(.AW(32), .DW(64), .IW(1), .TA(TA), .TT(TT)) drv = new(dbus[i]);

    initial begin
      @(posedge rst);
      drv.reset_slave();
      @(negedge rst);

      fork
        // Receive and process requests
        forever begin
          automatic logic [31:0]  addr;
          automatic logic         write;
          automatic logic [63:0]  data;
          automatic logic [7:0]   strb;
          automatic logic         id;
          automatic dresp_t       resp;
          automatic logic [63:0]  w_mask;
          // Receive
          write = 1'b0;
          drv.recv_req(addr, write, data, strb, id);
          resp.error = 1'b0;
          // Process Writes
          if (write && running) begin
            // IO
            case (addr)
              EocAddr:  -> evt_eoc;
              UartAddr: -> evt_uart_char;
              default: ;
            endcase
            //$display("Write to 0x%x: 0x%x, strobe 0b%b", addr ,data, strb);
            for (int i = 0; i < 8; i++) begin
              if (strb[i]) memory[addr >> 3][i*8 +: 8] = data[i*8 +: 8];
            end
          // Process Reads
          end else begin
            resp.data = memory[addr >> 3];
            //$display("Read from 0x%x: data 0x%x", addr, resp.data);
            resp_queue.put(resp);
          end
        end
        // Feed queued responses
        forever begin
          automatic dresp_t resp;
          resp_queue.get(resp);
          drv.send_rsp(resp.data, resp.error, 1'b0);
        end
      join_any
    end
  end

  // -------------------- MULDIV Accelerator  --------------------

  snitch_shared_muldiv i_snitch_shared_muldiv (
    .clk_i            ( clk                 ),
    .rst_i            ( rst                 ),
    .acc_qaddr_i      ( acc_req_o.addr      ),
    .acc_qid_i        ( acc_req_o.id        ),
    .acc_qdata_op_i   ( acc_req_o.data_op   ),
    .acc_qdata_arga_i ( acc_req_o.data_arga ),
    .acc_qdata_argb_i ( acc_req_o.data_argb ),
    .acc_qdata_argc_i ( acc_req_o.data_argc ),
    .acc_qvalid_i     ( acc_qvalid_o        ),
    .acc_qready_o     ( acc_qready_i        ),
    .acc_pdata_o      ( acc_resp_i.data     ),
    .acc_pid_o        ( acc_resp_i.id       ),
    .acc_perror_o     ( acc_resp_i.error    ),
    .acc_pvalid_o     ( acc_pvalid_i        ),
    .acc_pready_i     ( acc_pready_o        )
  );

  // -------------------- Testbench tasks --------------------

  // Initial reset
  initial begin
    rst = 0;
    #(10*TCK);
    rst = 1;
    #(10*TCK);
    rst = 0;
  end

  // axi reset
  initial begin
    axi_rst_n = 0;
    #(19.5*TCK);
    axi_rst_n = 1;
  end

  // Generate clock
  initial begin
    while (!eoc) begin
      clk = 1;
      #(TCK/2);
      clk = 0;
      #(TCK/2);
    end
    // Extra cycle for return code
    clk = 1;
    #(TCK/2);
    clk = 0;
    #(TCK/2);
  end

  // Wait for reset to complete
  task reset_start;
    @(posedge rst);
  endtask

  task reset_end;
    @(negedge rst);
    @(posedge clk);
  endtask

  // Let the core complex run to completion
  task run;
    running = 1'b1;
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

endmodule
