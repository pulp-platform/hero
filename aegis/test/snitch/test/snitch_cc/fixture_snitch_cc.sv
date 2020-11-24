module fixture_snitch_cc;
  import snitch_pkg::*;
  import reqrsp_test::*;

  import "DPI-C" function read_elf(input string filename);
  import "DPI-C" function byte get_section(output longint address, output longint len);
  import "DPI-C" context function byte read_section(input longint address, inout byte buffer[]);

  localparam TCK  = 1ns;
  localparam TA   = 0.2ns;  // must be nonzero to avoid Snitch load fifo double pop glitch
  localparam TT   = 0.8ns;

  // Addresses
  localparam logic [31:0] BootAddr      = 32'h8001_0000;
  localparam logic [31:0] UartAddr      = 32'hC000_0000;
  localparam logic [31:0] EocAddr       = 32'hD000_0000;

  logic rst, rst_n;
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

  REQRSP_BUS #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(64),
    .ID_WIDTH(1)
  ) dbus [2] (clk);

  // DUT
  snitch_cc #(
    .BootAddr (BootAddr)
  ) dut (
    .clk_i          ( clk             ),
    .rst_i          ( rst             ),
    .hart_id_i      ( '0              ),
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
    // Core Events
    .core_events_o  ( core_events_o   )
  );

  // -------------------- Memory System --------------------

  // Memory
  logic [63:0] memory [bit [28:0]];

  // Initialize peripheral registers
  initial begin
    memory[BootAddr                        >> 3] = 64'h0;
    memory[snitch_pkg::TCDMStartAddressReg >> 3] = 64'h0;
    memory[snitch_pkg::TCDMEndAddressReg   >> 3] = 64'h1000_0000;
    // for (int i = 0; i < memory[snitch_pkg::TCDMEndAddressReg >> 3] >> 3; i++) memory[i] = 0;
    memory[snitch_pkg::NrCoresReg          >> 3] = 64'h1;
    memory[snitch_pkg::BarrierReg          >> 3] = 64'h0;
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
