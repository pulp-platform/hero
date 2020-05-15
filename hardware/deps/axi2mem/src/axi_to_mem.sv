// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Andreas Kurth <akurth@iis.ee.ethz.ch>

module axi_to_mem #(
  parameter type         axi_req_t  = logic, // AXI request type
  parameter type         axi_resp_t = logic, // AXI response type
  parameter int unsigned AddrWidth  = 0,     // address width
  parameter int unsigned DataWidth  = 0,     // AXI data width
  parameter int unsigned IdWidth    = 0,     // AXI ID width
  parameter int unsigned NumBanks   = 0,     // number of banks at output
  parameter int unsigned BufDepth   = 1,     // depth of memory response buffer
  // Dependent parameters, do not override.
  parameter type addr_t     = logic [AddrWidth-1:0],
  parameter type mem_atop_t = logic [5:0],
  parameter type mem_data_t = logic [DataWidth/NumBanks-1:0],
  parameter type mem_strb_t = logic [DataWidth/NumBanks/8-1:0]
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  output logic                      busy_o,

  input  axi_req_t                  axi_req_i,
  output axi_resp_t                 axi_resp_o,

  output logic      [NumBanks-1:0]  mem_req_o,
  input  logic      [NumBanks-1:0]  mem_gnt_i,
  output addr_t     [NumBanks-1:0]  mem_addr_o,   // byte address
  output mem_data_t [NumBanks-1:0]  mem_wdata_o,  // write data
  output mem_strb_t [NumBanks-1:0]  mem_strb_o,   // byte-wise strobe
  output mem_atop_t [NumBanks-1:0]  mem_atop_o,   // atomic operation
  output logic      [NumBanks-1:0]  mem_we_o,     // write enable
  input  logic      [NumBanks-1:0]  mem_rvalid_i, // response valid
  input  mem_data_t [NumBanks-1:0]  mem_rdata_i   // read data
);

  typedef logic [DataWidth-1:0]   axi_data_t;
  typedef logic [DataWidth/8-1:0] axi_strb_t;
  typedef logic [IdWidth-1:0]     axi_id_t;

  typedef struct packed {
    addr_t      addr;
    mem_atop_t  atop;
    axi_strb_t  strb;
    axi_data_t  wdata;
    logic       we;
  } mem_req_t;

  typedef struct packed {
    addr_t          addr;
    axi_pkg::atop_t atop;
    axi_id_t        id;
    logic           last;
    axi_pkg::qos_t  qos;
    axi_pkg::size_t size;
    logic           write;
  } meta_t;

  axi_data_t      mem_rdata,
                  m2s_resp;
  axi_pkg::len_t  r_cnt_d,        r_cnt_q,
                  w_cnt_d,        w_cnt_q;
  logic           arb_valid,      arb_ready,
                  rd_valid,       rd_ready,
                  wr_valid,       wr_ready,
                  sel_b,          sel_buf_b,
                  sel_r,          sel_buf_r,
                  sel_valid,      sel_ready,
                  sel_buf_valid,  sel_buf_ready,
                  sel_lock_d,     sel_lock_q,
                  meta_valid,     meta_ready,
                  meta_buf_valid, meta_buf_ready,
                  meta_sel_d,     meta_sel_q,
                  m2s_req_valid,  m2s_req_ready,
                  m2s_resp_valid, m2s_resp_ready,
                  mem_req_valid,  mem_req_ready,
                  mem_rvalid;
  mem_req_t       m2s_req,
                  mem_req;
  meta_t          rd_meta,
                  rd_meta_d,      rd_meta_q,
                  wr_meta,
                  wr_meta_d,      wr_meta_q,
                  meta,           meta_buf;

  assign busy_o = axi_req_i.aw_valid | axi_req_i.ar_valid | axi_req_i.w_valid |
                    axi_resp_o.b_valid | axi_resp_o.r_valid |
                    (r_cnt_q > 0) | (w_cnt_q > 0);

  // Handle reads.
  always_comb begin
    // Default assignments
    axi_resp_o.ar_ready = 1'b0;
    rd_meta_d = rd_meta_q;
    rd_meta = 'x;
    rd_valid = 1'b0;
    r_cnt_d = r_cnt_q;
    // Handle R burst in progress.
    if (r_cnt_q > '0) begin
      rd_meta_d.last = (r_cnt_q == 8'd1);
      rd_meta = rd_meta_d;
      rd_meta.addr = rd_meta_q.addr + axi_pkg::num_bytes(rd_meta_q.size);
      rd_valid = 1'b1;
      if (rd_ready) begin
        r_cnt_d--;
        rd_meta_d.addr = rd_meta.addr;
      end
    // Handle new AR if there is one.
    end else if (axi_req_i.ar_valid) begin
      rd_meta_d = '{
        addr:   axi_pkg::aligned_addr(axi_req_i.ar.addr, axi_req_i.ar.size),
        atop:   '0,
        id:     axi_req_i.ar.id,
        last:   (axi_req_i.ar.len == '0),
        qos:    axi_req_i.ar.qos,
        size:   axi_req_i.ar.size,
        write:  1'b0
      };
      rd_meta = rd_meta_d;
      rd_meta.addr = axi_req_i.ar.addr;
      rd_valid = 1'b1;
      if (rd_ready) begin
        r_cnt_d = axi_req_i.ar.len;
        axi_resp_o.ar_ready = 1'b1;
      end
    end
  end

  // Handle writes.
  always_comb begin
    // Default assignments
    axi_resp_o.aw_ready = 1'b0;
    axi_resp_o.w_ready = 1'b0;
    wr_meta_d = wr_meta_q;
    wr_meta = 'x;
    wr_valid = 1'b0;
    w_cnt_d = w_cnt_q;
    // Handle W bursts in progress.
    if (w_cnt_q > '0) begin
      wr_meta_d.last = (w_cnt_q == 8'd1);
      wr_meta = wr_meta_d;
      wr_meta.addr = wr_meta_q.addr + axi_pkg::num_bytes(wr_meta_q.size);
      if (axi_req_i.w_valid) begin
        wr_valid = 1'b1;
        if (wr_ready) begin
          axi_resp_o.w_ready = 1'b1;
          w_cnt_d--;
          wr_meta_d.addr = wr_meta.addr;
        end
      end
    // Handle new AW if there is one.
    end else if (axi_req_i.aw_valid && axi_req_i.w_valid) begin
      wr_meta_d = '{
        addr:   axi_pkg::aligned_addr(axi_req_i.aw.addr, axi_req_i.aw.size),
        atop:   axi_req_i.aw.atop,
        id:     axi_req_i.aw.id,
        last:   (axi_req_i.aw.len == '0),
        qos:    axi_req_i.aw.qos,
        size:   axi_req_i.aw.size,
        write:  1'b1
      };
      wr_meta = wr_meta_d;
      wr_meta.addr = axi_req_i.aw.addr;
      wr_valid = 1'b1;
      if (wr_ready) begin
        w_cnt_d = axi_req_i.aw.len;
        axi_resp_o.aw_ready = 1'b1;
        axi_resp_o.w_ready = 1'b1;
      end
    end
  end

  // Arbitrate between reads and writes.
  stream_mux #(
    .DATA_T (meta_t),
    .N_INP  (2)
  ) i_ax_mux (
    .inp_data_i   ({wr_meta, rd_meta}),
    .inp_valid_i  ({wr_valid, rd_valid}),
    .inp_ready_o  ({wr_ready, rd_ready}),
    .inp_sel_i    (meta_sel_d),
    .oup_data_o   (meta),
    .oup_valid_o  (arb_valid),
    .oup_ready_i  (arb_ready)
  );
  always_comb begin
    meta_sel_d = meta_sel_q;
    sel_lock_d = sel_lock_q;
    if (sel_lock_q) begin
      meta_sel_d = meta_sel_q;
      if (arb_valid && arb_ready) begin
        sel_lock_d = 1'b0;
      end
    end else begin
      if (wr_valid ^ rd_valid) begin
        // If either write or read is valid but not both, select the valid one.
        meta_sel_d = wr_valid;
      end else if (wr_valid && rd_valid) begin
        // If both write and read are valid, decide according to QoS then burst properties.
        // Priorize higher QoS.
        if (wr_meta.qos > rd_meta.qos) begin
          meta_sel_d = 1'b1;
        end else if (rd_meta.qos > wr_meta.qos) begin
          meta_sel_d = 1'b0;
        // Decide requests with identical QoS.
        end else if (wr_meta.qos == rd_meta.qos) begin
          // 1. Priorize individual writes over read bursts.
          // Rationale: Read bursts can be interleaved on AXI but write bursts cannot.  However,
          // progress of read bursts must still be guaranteed, so this condition only applies if the
          // last beat granted was a read.
          if (wr_meta.last && !rd_meta.last && !meta_sel_q) begin
            meta_sel_d = 1'b1;
          // 2. Prioritize ongoing burst.
          // Rationale: Stalled bursts create backpressure or require costly buffers.
          end else if (w_cnt_q > '0) begin
            meta_sel_d = 1'b1;
          end else if (r_cnt_q > '0) begin
            meta_sel_d = 1'b0;
          // 3. Otherwise arbitrate round robin to prevent starvation.
          end else begin
            meta_sel_d = ~meta_sel_q;
          end
        end
      end
      // Lock arbitration if valid but not yet ready.
      if (arb_valid && !arb_ready) begin
        sel_lock_d = 1'b1;
      end
    end
  end

  // Fork arbitrated stream to meta data, memory requests, and R/B channel selection.
  stream_fork #(
    .N_OUP (3)
  ) i_fork (
    .clk_i,
    .rst_ni,
    .valid_i  (arb_valid),
    .ready_o  (arb_ready),
    .valid_o  ({sel_valid, meta_valid, m2s_req_valid}),
    .ready_i  ({sel_ready, meta_ready, m2s_req_ready})
  );

  assign sel_b = meta.write & meta.last;
  assign sel_r = ~meta.write | meta.atop[5];

  stream_fifo #(
    .FALL_THROUGH (1'b0),
    .DEPTH        (1 + BufDepth),
    .T            (logic[1:0])
  ) i_sel_buf (
    .clk_i,
    .rst_ni,
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     ({sel_b, sel_r}),
    .valid_i    (sel_valid),
    .ready_o    (sel_ready),
    .data_o     ({sel_buf_b, sel_buf_r}),
    .valid_o    (sel_buf_valid),
    .ready_i    (sel_buf_ready),
    .usage_o    (/* unused */)
  );

  stream_fifo #(
    .FALL_THROUGH (1'b0),
    .DEPTH        (1 + BufDepth),
    .T            (meta_t)
  ) i_meta_buf (
    .clk_i,
    .rst_ni,
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     (meta),
    .valid_i    (meta_valid),
    .ready_o    (meta_ready),
    .data_o     (meta_buf),
    .valid_o    (meta_buf_valid),
    .ready_i    (meta_buf_ready),
    .usage_o    (/* unused */)
  );

  // Map AXI ATOPs to RI5CY AMOs.
  always_comb begin
    m2s_req.atop = '0;
    m2s_req.wdata = axi_req_i.w.data;
    if (arb_valid && meta.atop[5:4] != axi_pkg::ATOP_NONE) begin
      m2s_req.atop[5] = 1'b1;
      if (meta.atop == axi_pkg::ATOP_ATOMICSWAP) begin
        m2s_req.atop[4:0] = riscv_defines::AMO_SWAP;
      end else begin
        case (meta.atop[2:0])
          axi_pkg::ATOP_ADD:  m2s_req.atop[4:0] = riscv_defines::AMO_ADD;
          axi_pkg::ATOP_CLR: begin
            m2s_req.atop[4:0] = riscv_defines::AMO_AND;
            m2s_req.wdata = ~axi_req_i.w.data;
          end
          axi_pkg::ATOP_EOR:  m2s_req.atop[4:0] = riscv_defines::AMO_XOR;
          axi_pkg::ATOP_SET:  m2s_req.atop[4:0] = riscv_defines::AMO_OR;
          axi_pkg::ATOP_SMAX: m2s_req.atop[4:0] = riscv_defines::AMO_MAX;
          axi_pkg::ATOP_SMIN: m2s_req.atop[4:0] = riscv_defines::AMO_MIN;
          axi_pkg::ATOP_UMAX: m2s_req.atop[4:0] = riscv_defines::AMO_MAXU;
          axi_pkg::ATOP_UMIN: m2s_req.atop[4:0] = riscv_defines::AMO_MINU;
        endcase
      end
    end
  end
  assign m2s_req.addr = meta.addr;
  assign m2s_req.strb = axi_req_i.w.strb;
  assign m2s_req.we = meta.write;

  // Interface memory as stream.
  mem_to_stream #(
    .mem_req_t  (mem_req_t),
    .mem_resp_t (axi_data_t),
    .BufDepth   (BufDepth)
  ) i_mem_to_stream (
    .clk_i,
    .rst_ni,
    .req_i            (m2s_req),
    .req_valid_i      (m2s_req_valid),
    .req_ready_o      (m2s_req_ready),
    .resp_o           (m2s_resp),
    .resp_valid_o     (m2s_resp_valid),
    .resp_ready_i     (m2s_resp_ready),
    .mem_req_o        (mem_req),
    .mem_req_valid_o  (mem_req_valid),
    .mem_req_ready_i  (mem_req_ready),
    .mem_resp_i       (mem_rdata),
    .mem_resp_valid_i (mem_rvalid)
  );

  // Split single memory request to desired number of banks.
  mem_to_banks #(
    .AddrWidth  (AddrWidth),
    .DataWidth  (DataWidth),
    .NumBanks   (NumBanks)
  ) i_mem_to_banks (
    .clk_i,
    .rst_ni,
    .req_i          (mem_req_valid),
    .gnt_o          (mem_req_ready),
    .addr_i         (mem_req.addr),
    .wdata_i        (mem_req.wdata),
    .strb_i         (mem_req.strb),
    .atop_i         (mem_req.atop),
    .we_i           (mem_req.we),
    .rvalid_o       (mem_rvalid),
    .rdata_o        (mem_rdata),
    .bank_req_o     (mem_req_o),
    .bank_gnt_i     (mem_gnt_i),
    .bank_addr_o    (mem_addr_o),
    .bank_wdata_o   (mem_wdata_o),
    .bank_strb_o    (mem_strb_o),
    .bank_atop_o    (mem_atop_o),
    .bank_we_o      (mem_we_o),
    .bank_rvalid_i  (mem_rvalid_i),
    .bank_rdata_i   (mem_rdata_i)
  );

  // Join memory read data and meta data stream.
  logic mem_join_valid, mem_join_ready;
  stream_join #(
    .N_INP (2)
  ) i_join (
    .inp_valid_i  ({m2s_resp_valid, meta_buf_valid}),
    .inp_ready_o  ({m2s_resp_ready, meta_buf_ready}),
    .oup_valid_o  (mem_join_valid),
    .oup_ready_i  (mem_join_ready)
  );

  // Dynamically fork the joined stream to B and R channels.
  stream_fork_dynamic #(
    .N_OUP  (2)
  ) i_fork_dynamic (
    .clk_i,
    .rst_ni,
    .valid_i      (mem_join_valid),
    .ready_o      (mem_join_ready),
    .sel_i        ({sel_buf_b, sel_buf_r}),
    .sel_valid_i  (sel_buf_valid),
    .sel_ready_o  (sel_buf_ready),
    .valid_o      ({axi_resp_o.b_valid, axi_resp_o.r_valid}),
    .ready_i      ({axi_req_i.b_ready, axi_req_i.r_ready})
  );

  // Compose B responses.
  assign axi_resp_o.b.id    = meta_buf.id;
  assign axi_resp_o.b.resp  = axi_pkg::RESP_OKAY;
  assign axi_resp_o.b.user  = '0;

  // Compose R responses.
  assign axi_resp_o.r.data  = m2s_resp;
  assign axi_resp_o.r.id    = meta_buf.id;
  assign axi_resp_o.r.last  = meta_buf.last;
  assign axi_resp_o.r.resp  = axi_pkg::RESP_OKAY;
  assign axi_resp_o.r.user  = '0;

  // Registers
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      meta_sel_q  <= 1'b0;
      sel_lock_q  <= 1'b0;
      rd_meta_q   <= '{default: '0};
      wr_meta_q   <= '{default: '0};
      r_cnt_q     <= '0;
      w_cnt_q     <= '0;
    end else begin
      meta_sel_q  <= meta_sel_d;
      sel_lock_q  <= sel_lock_d;
      rd_meta_q   <= rd_meta_d;
      wr_meta_q   <= wr_meta_d;
      r_cnt_q     <= r_cnt_d;
      w_cnt_q     <= w_cnt_d;
    end
  end

  // Assertions
  `ifndef VERILATOR
  `ifndef TARGET_SYNTHESIS
    default disable iff (!rst_ni);
    assume property (@(posedge clk_i)
        axi_req_i.ar_valid && !axi_resp_o.ar_ready |=> $stable(axi_req_i.ar))
      else $error("AR must remain stable until handshake has happened!");
    assert property (@(posedge clk_i)
        axi_resp_o.r_valid && !axi_req_i.r_ready |=> $stable(axi_resp_o.r))
      else $error("R must remain stable until handshake has happened!");
    assume property (@(posedge clk_i)
        axi_req_i.aw_valid && !axi_resp_o.aw_ready |=> $stable(axi_req_i.aw))
      else $error("AW must remain stable until handshake has happened!");
    assume property (@(posedge clk_i)
        axi_req_i.w_valid && !axi_resp_o.w_ready |=> $stable(axi_req_i.w))
      else $error("W must remain stable until handshake has happened!");
    assert property (@(posedge clk_i)
        axi_resp_o.b_valid && !axi_req_i.b_ready |=> $stable(axi_resp_o.b))
      else $error("B must remain stable until handshake has happened!");
    assert property (@(posedge clk_i) axi_req_i.ar_valid && axi_req_i.ar.len > 0 |->
        axi_req_i.ar.burst == axi_pkg::BURST_INCR)
      else $error("Non-incrementing bursts are not supported!");
    assert property (@(posedge clk_i) axi_req_i.aw_valid && axi_req_i.aw.len > 0 |->
        axi_req_i.aw.burst == axi_pkg::BURST_INCR)
      else $error("Non-incrementing bursts are not supported!");
    assert property (@(posedge clk_i) meta_valid && meta.atop != '0 |-> meta.write)
      else $warning("Unexpected atomic operation on read.");
  `endif
  `endif

endmodule
