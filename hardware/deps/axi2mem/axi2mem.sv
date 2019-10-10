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
// Andreas Kurth <akurth@iis.ee.ethz.ch>

module axi2mem #(
  parameter type axi_req_t = logic,     // AXI request type
  parameter type axi_resp_t = logic,    // AXI response type
  parameter int unsigned AddrWidth = 0, // address width
  parameter int unsigned DataWidth = 0, // AXI data width
  parameter int unsigned IdWidth = 0,   // AXI ID width
  parameter int unsigned NumBanks = 0,  // number of banks at output
  // Dependent parameters, do not override.
  localparam type addr_t = logic [AddrWidth-1:0],
  localparam type mem_atop_t = logic [5:0],
  localparam type mem_data_t = logic [DataWidth/NumBanks-1:0],
  localparam type mem_strb_t = logic [DataWidth/NumBanks/8-1:0]
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

  logic       mem_req,    mem_gnt,
              mem_we,
              mem_rvalid;
  addr_t      mem_addr;
  axi_data_t  mem_rdata,  mem_wdata;
  mem_atop_t  axi_atop,   mem_atop;

  axi_id_t                r_id;
  logic       b_ready,    r_ready,
              b_trigger,  r_trigger,
                          r_last;

  typedef enum logic [1:0] {
    READ, WRITE, BOTH
  } resp_arb_t;
  resp_arb_t  resp_arb_fifo_inp,
              resp_arb_fifo_oup;
  logic       resp_arb_fifo_full,
              resp_arb_fifo_push;

  assign busy_o = axi_req_i.aw_valid | axi_req_i.ar_valid | ~b_ready | ~r_ready;

  // Handle requests.
  assign r_last = 1'b1;
  always_comb begin
    axi_resp_o.ar_ready = 1'b0;
    axi_resp_o.aw_ready = 1'b0;
    axi_resp_o.w_ready = 1'b0;
    b_trigger = 1'b0;
    axi_atop = 'x;
    mem_req = 1'b0;
    mem_addr = 'x;
    mem_we = 1'bx;
    r_id = 'x;
    r_trigger = 1'b0;
    resp_arb_fifo_inp = resp_arb_t'('x);
    resp_arb_fifo_push = 1'b0;
    if (mem_gnt && !resp_arb_fifo_full) begin
      // Memory is ready for new requests.
      if (axi_req_i.aw_valid && axi_req_i.w_valid && b_ready) begin
        // AW and W are valid and B is ready to process the response.
        mem_addr = axi_req_i.aw.addr;
        axi_atop = axi_req_i.aw.atop;
        mem_we = 1'b1;
        if (axi_req_i.aw.atop[5]) begin
          // ATOP with R response
          if (r_ready) begin
            axi_resp_o.aw_ready = 1'b1;
            axi_resp_o.w_ready = 1'b1;
            mem_req = 1'b1;
            b_trigger = 1'b1;
            r_id = axi_req_i.aw.id;
            r_trigger = 1'b1;
            resp_arb_fifo_inp = BOTH;
            resp_arb_fifo_push = 1'b1;
          end
        end else begin
          // Regular write
          axi_resp_o.aw_ready = 1'b1;
          axi_resp_o.w_ready = 1'b1;
          mem_req = 1'b1;
          b_trigger = 1'b1;
          resp_arb_fifo_inp = WRITE;
          resp_arb_fifo_push = 1'b1;
        end
      end else if (axi_req_i.ar_valid && r_ready) begin
        // AR is valid and R is ready to process the response.
        axi_resp_o.ar_ready = 1'b1;
        mem_addr = axi_req_i.ar.addr;
        axi_atop = '0;
        mem_we = 1'b0;
        mem_req = 1'b1;
        r_id = axi_req_i.ar.id;
        r_trigger = 1'b1;
        resp_arb_fifo_inp = READ;
        resp_arb_fifo_push = 1'b1;
      end
    end
  end

  // Map AXI ATOPs to RI5CY AMOs.
  always_comb begin
    mem_atop = '0;
    mem_wdata = axi_req_i.w.data;
    if (axi_atop[5:4] != axi_pkg::ATOP_NONE) begin
      mem_atop[5] = 1'b1;
      if (axi_atop == axi_pkg::ATOP_ATOMICSWAP) begin
        mem_atop[4:0] = riscv_defines::AMO_SWAP;
      end else begin
        case (axi_atop[2:0])
          axi_pkg::ATOP_ADD:  mem_atop[4:0] = riscv_defines::AMO_ADD;
          axi_pkg::ATOP_CLR: begin
            mem_atop[4:0] = riscv_defines::AMO_AND;
            mem_wdata = ~axi_req_i.w.data;
          end
          axi_pkg::ATOP_EOR:  mem_atop[4:0] = riscv_defines::AMO_XOR;
          axi_pkg::ATOP_SET:  mem_atop[4:0] = riscv_defines::AMO_OR;
          axi_pkg::ATOP_SMAX: mem_atop[4:0] = riscv_defines::AMO_MAX;
          axi_pkg::ATOP_SMIN: mem_atop[4:0] = riscv_defines::AMO_MIN;
          axi_pkg::ATOP_UMAX: mem_atop[4:0] = riscv_defines::AMO_MAXU;
          axi_pkg::ATOP_UMIN: mem_atop[4:0] = riscv_defines::AMO_MINU;
        endcase
      end
    end
  end

  // Arbitrate between B and R responses.
  fifo_v3 #(
    .FALL_THROUGH (1'b1),
    .DATA_WIDTH   ($bits(resp_arb_t)),
    .DEPTH        (8),
    .dtype        (resp_arb_t)
  ) i_resp_arb_fifo (
    .clk_i,
    .rst_ni,
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .full_o     (resp_arb_fifo_full),
    .empty_o    (/* unused */),
    .data_i     (resp_arb_fifo_inp),
    .push_i     (resp_arb_fifo_push),
    .data_o     (resp_arb_fifo_oup),
    .pop_i      (mem_rvalid)
  );

  // Handle B responses.
  axi2mem_resp #(
    .data_t (axi_data_t),
    .id_t   (axi_id_t)
  ) i_b_resp (
    .clk_i,
    .rst_ni,
    .trigger_i    (b_trigger),
    .ready_o      (b_ready),
    .id_i         (axi_req_i.aw.id),
    .last_i       (/* unused */),
    .mem_valid_i  (mem_rvalid & (resp_arb_fifo_oup != READ)),
    .mem_data_i   (/* unused */),
    .axi_data_o   (/* unused */),
    .axi_id_o     (axi_resp_o.b.id),
    .axi_last_o   (/* unused */),
    .axi_resp_o   (axi_resp_o.b.resp),
    .axi_valid_o  (axi_resp_o.b_valid),
    .axi_ready_i  (axi_req_i.b_ready)
  );
  assign axi_resp_o.b.user = '0;

  // Handle R responses.
  axi2mem_resp #(
    .data_t (axi_data_t),
    .id_t   (axi_id_t)
  ) i_r_resp (
    .clk_i,
    .rst_ni,
    .trigger_i    (r_trigger),
    .ready_o      (r_ready),
    .id_i         (r_id),
    .last_i       (r_last),
    .mem_valid_i  (mem_rvalid & (resp_arb_fifo_oup != WRITE)),
    .mem_data_i   (mem_rdata),
    .axi_data_o   (axi_resp_o.r.data),
    .axi_id_o     (axi_resp_o.r.id),
    .axi_last_o   (axi_resp_o.r.last),
    .axi_resp_o   (axi_resp_o.r.resp),
    .axi_valid_o  (axi_resp_o.r_valid),
    .axi_ready_i  (axi_req_i.r_ready)
  );
  assign axi_resp_o.r.user = '0;

  // Split single memory request to desired number of banks.
  mem2banks #(
    .AddrWidth  (AddrWidth),
    .DataWidth  (DataWidth),
    .NumBanks   (NumBanks)
  ) i_mem2banks (
    .clk_i,
    .rst_ni,
    .req_i          (mem_req),
    .gnt_o          (mem_gnt),
    .addr_i         (mem_addr),
    .wdata_i        (mem_wdata),
    .strb_i         (axi_req_i.w.strb),
    .atop_i         (mem_atop),
    .we_i           (mem_we),
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
    assert property (@(posedge clk_i) axi_req_i.ar_valid |-> axi_req_i.ar.len == '0)
      else $error("Bursts are not supported yet!");
    assert property (@(posedge clk_i) axi_req_i.aw_valid |-> axi_req_i.aw.len == '0)
      else $error("Bursts are not supported yet!");
  `endif
  `endif

endmodule


`include "axi/assign.svh"
`include "axi/typedef.svh"
// Interface wrapper for axi2mem
module axi2mem_wrap #(
  parameter int unsigned AddrWidth = 0,
  parameter int unsigned DataWidth = 0,
  parameter int unsigned IdWidth = 0,
  parameter int unsigned UserWidth = 0,
  parameter int unsigned NumBanks = 0,
  // Dependent parameters, do not override.
  localparam type addr_t = logic [AddrWidth-1:0],
  localparam type mem_atop_t = logic [5:0],
  localparam type mem_data_t = logic [DataWidth/NumBanks-1:0],
  localparam type mem_strb_t = logic [DataWidth/NumBanks/8-1:0]
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  output logic                      busy_o,

  AXI_BUS.Slave                     slv,

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
  typedef logic [IdWidth-1:0]     id_t;
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  typedef logic [UserWidth-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T ( aw_chan_t, addr_t, id_t,         user_t);
  `AXI_TYPEDEF_W_CHAN_T  (  w_chan_t, data_t,       strb_t, user_t);
  `AXI_TYPEDEF_B_CHAN_T  (  b_chan_t,         id_t,         user_t);
  `AXI_TYPEDEF_AR_CHAN_T ( ar_chan_t, addr_t, id_t,         user_t);
  `AXI_TYPEDEF_R_CHAN_T  (  r_chan_t, data_t, id_t,         user_t);
  `AXI_TYPEDEF_REQ_T     (     req_t, aw_chan_t, w_chan_t, ar_chan_t);
  `AXI_TYPEDEF_RESP_T    (    resp_t,  b_chan_t, r_chan_t);
  req_t   req;
  resp_t  resp;
  `AXI_ASSIGN_TO_REQ    (req, slv);
  `AXI_ASSIGN_FROM_RESP (slv, resp);
  axi2mem #(
    .axi_req_t  (req_t),
    .axi_resp_t (resp_t),
    .AddrWidth  (AddrWidth),
    .DataWidth  (DataWidth),
    .IdWidth    (IdWidth),
    .NumBanks   (NumBanks)
  ) i_axi2mem (
    .clk_i,
    .rst_ni,
    .busy_o,
    .axi_req_i  (req),
    .axi_resp_o (resp),
    .mem_req_o,
    .mem_gnt_i,
    .mem_addr_o,
    .mem_wdata_o,
    .mem_strb_o,
    .mem_atop_o,
    .mem_we_o,
    .mem_rvalid_i,
    .mem_rdata_i
  );
endmodule


module axi2mem_resp #(
  parameter type data_t = logic,
  parameter type id_t = logic
) (
  input  logic            clk_i,
  input  logic            rst_ni,
  // Interface to request handler
  input  logic            trigger_i,
  output logic            ready_o,
  input  id_t             id_i,
  input  logic            last_i,
  // Interface to memory
  input  logic            mem_valid_i,
  input  data_t           mem_data_i,
  // Interface to AXI response channel
  output data_t           axi_data_o,
  output id_t             axi_id_o,
  output logic            axi_last_o,
  output axi_pkg::resp_t  axi_resp_o,
  output logic            axi_valid_o,
  input  logic            axi_ready_i
);

  enum logic [1:0] {
    Ready, Wait, Hold
  }       state_d,  state_q;
  data_t  data_d,   data_q;
  id_t    id_d,     id_q;
  logic   last_d,   last_q;

  always_comb begin
    // Response is always valid in Hold state, otherwise it depends on valid from memory for
    // feedthrough.
    unique case (state_q)
      Ready:    axi_valid_o = trigger_i & mem_valid_i;
      Wait:     axi_valid_o = mem_valid_i;
      Hold:     axi_valid_o = 1'b1;
      default:  axi_valid_o = 1'b0;
    endcase

    // Latch data from memory if it is valid and we are waiting for it.
    unique casez ({state_q, trigger_i, mem_valid_i})
      {Ready, 1'b1, 1'b1},
      {Wait,  1'b?, 1'b1}:  data_d = mem_data_i;
      default:              data_d = data_q;
    endcase

    // Hold state by default.
    state_d = state_q;
    // If triggered but data from memory not valid, wait for it.
    if (trigger_i && !mem_valid_i) begin
      state_d = Wait;
    end
    // If response is valid and ready, go back to ready, otherwise hold.
    if (axi_valid_o) begin
      state_d = axi_ready_i ? Ready : Hold;
    end

    // Ready to accept triggers only in ready state.
    ready_o = state_q == Ready;
  end
  always_comb begin
    id_d = id_q;
    last_d = last_q;
    if (trigger_i && ready_o) begin
      id_d = id_i;
      last_d = last_i;
    end
  end
  assign axi_data_o = data_d;
  assign axi_id_o   = id_d;
  assign axi_resp_o = axi_pkg::RESP_OKAY;
  assign axi_last_o = last_d;

  // Registers
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      data_q  <=   '0;
      id_q    <=   '0;
      last_q  <= 1'b0;
      state_q <= Ready;
    end else begin
      data_q  <= data_d;
      id_q    <= id_d;
      last_q  <= last_d;
      state_q <= state_d;
    end
  end

  // Assertions
  `ifndef VERILATOR
  `ifndef TARGET_SYNTHESIS
    default disable iff (!rst_ni);
    assert property (@(posedge clk_i) trigger_i |-> ready_o) else $error("Lost trigger!");
  `endif
  `endif

endmodule


// Split memory access over multiple parallel banks, where each bank has its own req/gnt request and
// valid response direction.
module mem2banks #(
  parameter int unsigned AddrWidth = 0, // input address width
  parameter int unsigned DataWidth = 0, // input data width, must be a power of two
  parameter int unsigned NumBanks = 0,  // number of banks at output, must evenly divide the data
                                        // width
  // Dependent parameters, do not override.
  localparam type addr_t = logic [AddrWidth-1:0],
  localparam type atop_t = logic [5:0],
  localparam type inp_data_t = logic [DataWidth-1:0],
  localparam type inp_strb_t = logic [DataWidth/8-1:0],
  localparam type oup_data_t = logic [DataWidth/NumBanks-1:0],
  localparam type oup_strb_t = logic [DataWidth/NumBanks/8-1:0]
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  input  logic                      req_i,
  output logic                      gnt_o,
  input  addr_t                     addr_i,
  input  inp_data_t                 wdata_i,
  input  inp_strb_t                 strb_i,
  input  atop_t                     atop_i,
  input  logic                      we_i,
  output logic                      rvalid_o,
  output inp_data_t                 rdata_o,

  output logic      [NumBanks-1:0]  bank_req_o,
  input  logic      [NumBanks-1:0]  bank_gnt_i,
  output addr_t     [NumBanks-1:0]  bank_addr_o,
  output oup_data_t [NumBanks-1:0]  bank_wdata_o,
  output oup_strb_t [NumBanks-1:0]  bank_strb_o,
  output atop_t     [NumBanks-1:0]  bank_atop_o,
  output logic      [NumBanks-1:0]  bank_we_o,
  input  logic      [NumBanks-1:0]  bank_rvalid_i,
  input  oup_data_t [NumBanks-1:0]  bank_rdata_i
);

  localparam DataBytes = $bits(inp_strb_t);
  localparam BitsPerBank  = $bits(oup_data_t);
  localparam BytesPerBank = $bits(oup_strb_t);

  typedef struct packed {
    addr_t      addr;
    oup_data_t  wdata;
    oup_strb_t  strb;
    atop_t      atop;
    logic       we;
  } req_t;

  logic                 req_valid;
  logic [NumBanks-1:0]              req_ready,
                        resp_valid, resp_ready;
  req_t [NumBanks-1:0]  bank_req,
                        bank_oup;

  function automatic addr_t align_addr(input addr_t addr);
    return (addr >> $clog2(DataBytes)) << $clog2(DataBytes);
  endfunction

  // Handle requests.
  assign req_valid = req_i & gnt_o;
  for (genvar i = 0; i < NumBanks; i++) begin : gen_reqs
    assign bank_req[i].addr   = align_addr(addr_i) + i * BytesPerBank;
    assign bank_req[i].wdata  = wdata_i[i*BitsPerBank+:BitsPerBank];
    assign bank_req[i].strb   = strb_i[i*BytesPerBank+:BytesPerBank];
    assign bank_req[i].atop   = atop_i;
    assign bank_req[i].we     = we_i;
    fall_through_register #(
      .T  (req_t)
    ) i_ft_reg (
      .clk_i,
      .rst_ni,
      .clr_i      (1'b0),
      .testmode_i (1'b0),
      .valid_i    (req_valid),
      .ready_o    (req_ready[i]),
      .data_i     (bank_req[i]),
      .valid_o    (bank_req_o[i]),
      .ready_i    (bank_gnt_i[i]),
      .data_o     (bank_oup[i])
    );
    assign bank_addr_o[i]   = bank_oup[i].addr;
    assign bank_wdata_o[i]  = bank_oup[i].wdata;
    assign bank_strb_o[i]   = bank_oup[i].strb;
    assign bank_atop_o[i]   = bank_oup[i].atop;
    assign bank_we_o[i]     = bank_oup[i].we;
  end

  // Grant output if all our requests have been granted.
  assign gnt_o = (&req_ready) & (&resp_ready);

  // Handle responses.
  for (genvar i = 0; i < NumBanks; i++) begin : gen_resp_regs
    fall_through_register #(
      .T  (oup_data_t)
    ) i_ft_reg (
      .clk_i,
      .rst_ni,
      .clr_i      (1'b0),
      .testmode_i (1'b0),
      .valid_i    (bank_rvalid_i[i]),
      .ready_o    (resp_ready[i]),
      .data_i     (bank_rdata_i[i]),
      .data_o     (rdata_o[i*BitsPerBank+:BitsPerBank]),
      .ready_i    (rvalid_o),
      .valid_o    (resp_valid[i])
    );
  end
  assign rvalid_o = &resp_valid;

  // Assertions
  `ifndef VERILATOR
  `ifndef TARGET_SYNTHESIS
    initial begin
      assume (DataWidth != 0 && (DataWidth & (DataWidth - 1)) == 0)
        else $fatal(1, "Data width must be a power of two!");
      assume (DataWidth % NumBanks == 0)
        else $fatal(1, "Data width must be evenly divisible over banks!");
      assume ((DataWidth / NumBanks) % 8 == 0)
        else $fatal(1, "Data width of each bank must be divisible into 8-bit bytes!");
    end
  `endif
  `endif

endmodule
