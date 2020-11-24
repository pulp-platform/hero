`include "axi/assign.svh"

import "DPI-C" function read_elf(input string filename);
import "DPI-C" function byte get_section(output longint address, output longint len);
import "DPI-C" context function byte read_section(input longint address, inout byte buffer[]);

module fixture_billywig;
  parameter TCK = 2ns;
  parameter TCK_DDR = 5ns;
  parameter TCK_JTAG = 5ns;
  parameter bit CHECK_DATA = 0;
  parameter DDR_IN_DELAY = 0ns;
  parameter DDR_OUT_DELAY = 0ns;

  wire clk_dut;
  wire clk_x_dut;
  wire testmode_dut;
  wire scan_en_dut;
  wire rst_n_dut;
  wire tck_dut;
  wire trst_n_dut;
  wire tms_dut;
  wire tdi_dut;
  wire tdo_dut;

  logic clk_i = 0;
  logic clk_x_i = 0;
  logic testmode_i = 0;
  logic scan_en_i = 0;
  bit eoc = 0;
  logic rst_ni;

  logic tck_i = 0;
  JTAG_DV jtag_mst (tck_i);

  logic [3:0] ddr_in_dut;
  logic [3:0] ddr_out_dut;

  wire  ddr_clk_dut;
  wire [3:0] ddr_dut_out, ddr_dut_in;
  logic [3:0] ddr_tb_out, ddr_tb_in;
  logic [3:0] ddr_dut_out_var, ddr_dut_in_var;

  logic  ddr_clk_i = 0;

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( billywig_axi_pkg::AddrWidth  ),
    .AXI_DATA_WIDTH ( billywig_axi_pkg::DataWidth  ),
    .AXI_ID_WIDTH   ( billywig_pkg::IdWidth        ),
    .AXI_USER_WIDTH ( billywig_axi_pkg::UserWidth  )
  ) master(clk_i);

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( billywig_axi_pkg::AddrWidth  ),
    .AXI_DATA_WIDTH ( billywig_axi_pkg::DataWidth  ),
    .AXI_ID_WIDTH   ( billywig_pkg::IdWidth        ),
    .AXI_USER_WIDTH ( billywig_axi_pkg::UserWidth  )
  ) master_dut();

  `AXI_ASSIGN(master_dut, master)

  billywig_axi_pkg::req_t      serial_in_req;
  billywig_axi_pkg::resp_t     serial_in_resp;
  billywig_axi_pkg::req_slv_t  serial_out_req;
  billywig_axi_pkg::resp_slv_t serial_out_resp;

  assign serial_out_resp = '0;

  logic [63:0] memory[bit [31:0]];
  int sections [bit [31:0]];

  AXI_BUS slave();

  `AXI_ASSIGN_TO_REQ(serial_in_req, master_dut)
  `AXI_ASSIGN_FROM_RESP(master_dut, serial_in_resp)

  snitch_serial_link #(
    .axi_in_req_t   ( billywig_axi_pkg::req_t      ),
    .axi_in_resp_t  ( billywig_axi_pkg::resp_t     ),
    .axi_out_req_t  ( billywig_axi_pkg::req_slv_t  ),
    .axi_out_resp_t ( billywig_axi_pkg::resp_slv_t )
  ) i_serial (
    .clk_i          ( clk_i           ),
    .rst_ni         ( rst_ni          ),
    .testmode_i     ( 1'b0            ),
    .axi_in_req_i   ( serial_in_req   ),
    .axi_in_resp_o  ( serial_in_resp  ),
    .axi_out_req_o  ( serial_out_req  ),
    .axi_out_resp_i ( serial_out_resp ),
    .ddr_clk_i      ( ddr_clk_i       ),
    .ddr_i          ( ddr_tb_in       ),
    .ddr_o          ( ddr_tb_out      )
  );

  billywig i_billywig (
    .clk_i      ( clk_dut       ),
    .clk_x_i    ( clk_x_dut     ),
    .testmode_i ( testmode_dut  ),
    .scan_en_i  ( scan_en_dut   ),
    .scan_in_i  ( /* open */    ),
    .scan_out_o ( /* open */    ),
    .rst_ni     ( rst_n_dut     ),
    .tck_i      ( tck_dut       ),
    .trst_ni    ( trst_n_dut    ),
    .tms_i      ( tms_dut       ),
    .tdi_i      ( tdi_dut       ),
    .tdo_o      ( tdo_dut       ),
    .ddr_clk_i  ( ddr_clk_dut   ),
    .ddr_i      ( ddr_dut_in    ),
    .ddr_o      ( ddr_dut_out   )
  );

  assign clk_dut = clk_i;
  assign clk_x_dut = clk_x_i;
  assign testmode_dut = testmode_i;
  assign scan_en_dut = scan_en_i;
  assign rst_n_dut = rst_ni;
  assign tck_dut = tck_i;

  assign trst_n_dut = jtag_mst.trst_n;
  assign tms_dut = jtag_mst.tms;
  assign tdi_dut = jtag_mst.tdi;
  assign jtag_mst.tdo = tdo_dut;

  assign ddr_clk_dut = ddr_clk_i;
  assign ddr_dut_out_var = ddr_dut_out;
  assign ddr_dut_in = ddr_dut_in_var;
  always @(ddr_tb_out) ddr_dut_in_var <= #(0.25*TCK_DDR+DDR_IN_DELAY) ddr_tb_out;
  always @(ddr_dut_out_var) ddr_tb_in <= #(0.25*TCK_DDR+DDR_OUT_DELAY) ddr_dut_out_var;

  initial begin
    rst_ni = 1;
    jtag_mst.trst_n = 1;
    #100ns;
    rst_ni = 0;
    jtag_mst.trst_n = 0;
    #100ns;
    rst_ni = 1;
    jtag_mst.trst_n = 1;
  end

  // Generate clock.
  initial begin
    @(negedge rst_ni);
    @(posedge rst_ni);
    #100ns;
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

  // Generate clock.
  initial begin
    @(negedge rst_ni);
    @(posedge rst_ni);
    #100ns;
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

  // Generate clock.
  initial begin
    @(negedge jtag_mst.trst_n);
    @(posedge jtag_mst.trst_n);
    #100ns;
    while (!eoc) begin
      tck_i = 1;
      #(TCK_JTAG/2);
      tck_i = 0;
      #(TCK_JTAG/2);
    end
    repeat (8) begin
      tck_i = 1;
      #(TCK_JTAG/2);
      tck_i = 0;
      #(TCK_JTAG/2);
    end
  end

  // Let the cluster run to completion.
  task run;
    @(posedge clk_i iff eoc == 1);
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

  // Wait for reset to complete.
  task wait_for_reset;
    @(negedge rst_ni);
    @(posedge rst_ni);
    @(posedge clk_i);
  endtask

  typedef jtag_test::riscv_dbg#(.IrLength(5), .TA(0.1*TCK_JTAG), .TT(0.9*TCK_JTAG)) riscv_dbg_t;
  riscv_dbg_t::jtag_driver_t jtag_in = new (jtag_mst);
  riscv_dbg_t riscv_dbg = new(jtag_in);

  // Pre-load using JTAG and SBA
  task preload_jtag;
    logic [31:0] idcode;
    logic [63:0] rdata;
    logic [31:0] scratch;
    automatic dm::sbcs_t sbcs = '{
      sbautoincrement: 1'b1,
      sbreadondata: 1'b1,
      sbasize: 3,
      default: '0
    };
    @(negedge rst_ni);
    @(posedge rst_ni);
    $display("Preload using JTAG");
    // riscv_dbg.reset_master();
    // @(posedge clk_i);
    riscv_dbg.get_idcode(idcode);
    // check ID code to match
    assert (idcode == billywig_pkg::IDCode) else $error("IDCode Mismatch (%h (act) != %h (exp))", idcode, billywig_pkg::IDCode);
    $display("IDCODE %h", idcode);
    // activate debug module
    riscv_dbg.write_dmi(dm::DMControl, 32'h0000_0001);

    // Write sections.
    riscv_dbg.write_dmi(dm::SBCS, sbcs);
    foreach (sections[addr]) begin
      $display("Writing %h (%0d words)", addr << 3, sections[addr]);
      riscv_dbg.write_dmi(dm::SBAddress0, (addr << 3));
      for (int i = 0; i < sections[addr]; i++) begin
        if (i % 20 == 0)
          $display(" - Word %0d/%0d (%0d%%)", i, sections[addr], i*100/(sections[addr]-1));
        riscv_dbg.write_dmi(dm::SBData1, memory[addr + i][63:32]);
        riscv_dbg.write_dmi(dm::SBData0, memory[addr + i][31:0]);
      end
    end

    // Read sections and check.
    if (CHECK_DATA) begin
      sbcs.sbreadonaddr = 1;
      riscv_dbg.write_dmi(dm::SBCS, sbcs);
      foreach (sections[addr]) begin
        $display("Checking %h (%0d words)", addr << 3, sections[addr]);
        riscv_dbg.write_dmi(dm::SBAddress0, (addr << 3));
        for (int i = 0; i < sections[addr]; i++) begin
          if (i % 20 == 0)
            $display(" - Word %0d/%0d (%0d%%)", i, sections[addr], i*100/(sections[addr]-1));
          riscv_dbg.read_dmi(dm::SBData1, rdata[63:32], 10);
          riscv_dbg.read_dmi(dm::SBData0, rdata[31:0], 10);
          if (rdata != memory[addr + i])
            $error("Readback mismatch: %h, act %h != exp %h", (addr + i) << 3, rdata, memory[addr + i]);
        end
      end
    end

    // Start execution.
    $info("Setting fetch enable");
    sbcs.sbreadonaddr = 0;
    sbcs.sbasize = 2;
    riscv_dbg.write_dmi(dm::SBCS, sbcs);
    riscv_dbg.write_dmi(dm::SBAddress0, snitch_cfg::ClusterPeriphStartAddress+snitch_pkg::FetchEnableReg);
    riscv_dbg.write_dmi(dm::SBData0, 32'h0000_000F);
    $info("Waking up cores");
    riscv_dbg.write_dmi(dm::SBAddress0, snitch_cfg::ClusterPeriphStartAddress+snitch_pkg::WakeUpReg);
    riscv_dbg.write_dmi(dm::SBData0, 32'h0000_000F);

    // Wait for scratch register to be set to non-zero value.
    $info("Waiting for completion");
    sbcs.sbreadonaddr = 1;
    sbcs.sbautoincrement = 0;
    riscv_dbg.write_dmi(dm::SBCS, sbcs);
    riscv_dbg.write_dmi(dm::SBAddress0, snitch_cfg::ClusterPeriphStartAddress+snitch_pkg::ScratchReg);
    do begin
      riscv_dbg.wait_idle(10);
      riscv_dbg.read_dmi(dm::SBData0, scratch);
    end while (scratch == 0);
    void'(exit(scratch));
  endtask

  typedef axi_test::axi_driver #(.AW(billywig_axi_pkg::AddrWidth), .DW(billywig_axi_pkg::DataWidth), .IW(billywig_pkg::IdWidth), .UW(billywig_axi_pkg::UserWidth), .TA(0.1*TCK), .TT(0.9*TCK)) driver_in_t;
  driver_in_t driver_in = new(master);

  // Reset AXI.
  initial begin
    @(negedge rst_ni);
    driver_in.reset_master();
    @(posedge rst_ni);
  end

  // Reset JTAG.
  initial begin
    @(negedge jtag_mst.trst_n);
    jtag_mst.tdi = 0;
    jtag_mst.tms = 1;
    @(posedge jtag_mst.trst_n);
  end

  // TODO(zarubaf): Break apart on 4k page boundary
  // TODO(zarubaf): Add error flags
  // Write `len` words beginning from `addr` taken from `data`
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
  // Read `len` words beginning from `addr` and store it in `data`
  task automatic axi_read(input logic [31:0] addr, input int len, ref logic [63:0] data [$]);
    automatic driver_in_t::ax_beat_t ax = new();
    automatic driver_in_t::r_beat_t r;
    automatic int i = 0;
    // $display("Reading %h (%0d words)", addr, len);
    ax.ax_addr = addr;
    ax.ax_id = '0;
    ax.ax_len = len - 1;
    ax.ax_size = 3;
    driver_in.send_ar(ax);
    do begin
      driver_in.recv_r(r);
      // $display("read %h[%d] data=%h last=%b", addr, i, r.r_data, r.r_last);
      data.push_back(r.r_data);
      i++;
    end while (!r.r_last);
    // $display("read is over");
  endtask

  // Preload using AXI over Serial
  task preload_axi();
    automatic logic [63:0] scratch [$];
    wait_for_reset();
    $display("Preload using AXI");
    foreach (sections[addr]) begin
      automatic logic [63:0] data [$];
      // push the data section into a fifo
      for (int i = 0; i < sections[addr]; i++) data.push_back(memory[addr + i]);
      $display("Writing %h (%0d words)", addr << 3, $size(data));
      axi_write(addr << 3, $size(data), data);
    end
    $display("Preload done");
    if (CHECK_DATA) begin
      foreach (sections[addr]) begin
        automatic logic [63:0] data [$];
        $display("Checking %h (%0d words)", addr << 3, sections[addr]);
        axi_read(addr << 3, sections[addr], data);
        for (int i = 0; i < sections[addr]; i++) begin
          if (data[i] != memory[addr + i])
            $error("Readback mismatch: %h, act %h != exp %h", (addr + i) << 3, data[i], memory[addr + i]);
        end
      end
      $display("Readback done");
    end
    begin
      automatic logic [63:0] data [$];
      data.push_back(32'h0000_000F);
      $info("Setting fetch enable");
      axi_write(snitch_cfg::ClusterPeriphStartAddress+snitch_pkg::FetchEnableReg, 1, data);
    end
    begin
      automatic logic [63:0] data [$];
      data.push_back(32'h0000_000F);
      $info("Waking up cores");
      axi_write(snitch_cfg::ClusterPeriphStartAddress+snitch_pkg::WakeUpReg, 1, data);
    end
    // Wait for scratch register to be set to non-zero value.
    $info("Waiting for completion");
    do begin
      scratch = {};
      repeat (100) @(posedge clk_i);
      axi_read(snitch_cfg::ClusterPeriphStartAddress+snitch_pkg::ScratchReg, 1, scratch);
    end while (scratch[0] == 0);
    void'(exit(scratch[0]));
  endtask

  function void exit(logic [63:0] code);
    eoc = 1;
    // Report the exit code.
    code >>= 1;
    if (code)
      $error("Execution FAILED: Exit code 0x%h, %0d", code, code);
    else
      $info("Execution SUCCESSFUL");
  endfunction
endmodule
