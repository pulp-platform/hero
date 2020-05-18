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

// Split memory access over multiple parallel banks, where each bank has its own req/gnt request and
// valid response direction.
module mem_to_banks #(
  parameter int unsigned AddrWidth = 0, // input address width
  parameter int unsigned DataWidth = 0, // input data width, must be a power of two
  parameter int unsigned NumBanks = 0,  // number of banks at output, must evenly divide the data
                                        // width
  // Dependent parameters, do not override.
  parameter type addr_t = logic [AddrWidth-1:0],
  parameter type atop_t = logic [5:0],
  parameter type inp_data_t = logic [DataWidth-1:0],
  parameter type inp_strb_t = logic [DataWidth/8-1:0],
  parameter type oup_data_t = logic [DataWidth/NumBanks-1:0],
  parameter type oup_strb_t = logic [DataWidth/NumBanks/8-1:0]
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
