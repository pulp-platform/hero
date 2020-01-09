// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module soc_periph_fifo
#(
  parameter ID_WIDTH = 8,
  parameter FIFO_DEPTH = 4
)
(
  // clock and reset
  input  logic clk_i,
  input  logic rst_ni,

  output logic incoming_evt_o,

  // bus for incoming event ids
  input  logic                fifo_data_valid_i,
  output logic                fifo_fulln_o,
  input  logic [ID_WIDTH-1:0] fifo_data_i,

  // bus to read the oldest event id
  XBAR_PERIPH_BUS.Slave periph_int_bus_slave
);

  localparam LOG_FIFO_DEPTH = $clog2(FIFO_DEPTH);

  // FIFO data and r/w-pointers
  logic [FIFO_DEPTH-1:0][ID_WIDTH-1:0] fifo_data_DP, fifo_data_DN;
  logic [FIFO_DEPTH-1:0]               entry_valid_SP, entry_valid_SN;
  logic [LOG_FIFO_DEPTH-1:0]           r_ptr_SP, r_ptr_SN, w_ptr_SP, w_ptr_SN;
  logic                                r_req_del_SP, r_req_del_SN;

  // control logic
  logic fifo_full, fifo_empty;

  assign fifo_full  = (w_ptr_SP == r_ptr_SP) && (entry_valid_SP[r_ptr_SP] == 1'b1);
  assign fifo_empty = (w_ptr_SP == r_ptr_SP) && (entry_valid_SP[r_ptr_SP] == 1'b0);

  // flag incoming event to event buffers
  assign incoming_evt_o = ~fifo_empty;
  // stall message producers once we have no further space
  assign fifo_fulln_o   = ~fifo_full;
  // no stall functionality
  assign periph_int_bus_slave.gnt = periph_int_bus_slave.req;

  // for LINT
  assign periph_int_bus_slave.r_opc = 1'b0;
  assign periph_int_bus_slave.r_id  = '0;

  // R/W logic
  always_comb begin
    w_ptr_SN        = w_ptr_SP;
    r_ptr_SN        = r_ptr_SP;
    r_req_del_SN    = 1'b0;
    fifo_data_DN    = fifo_data_DP;
    entry_valid_SN  = entry_valid_SP;

    // important for top-level bus mux
    periph_int_bus_slave.r_rdata  = '0;
    periph_int_bus_slave.r_valid  = 1'b0;

    // store new id and move write pointer if there is space
    if (fifo_data_valid_i & ~fifo_full) begin
      fifo_data_DN[w_ptr_SP]   = fifo_data_i;
      entry_valid_SN[w_ptr_SP] = 1'b1;
      w_ptr_SN = (w_ptr_SP + 1) % FIFO_DEPTH;
    end

    if (periph_int_bus_slave.req & periph_int_bus_slave.wen)
      r_req_del_SN = 1'b1;

    // react to delayed read request, move read pointer if we don't read an empty FIFO
    if (r_req_del_SP) begin
      periph_int_bus_slave.r_rdata[31]           = entry_valid_SP[r_ptr_SP];
      periph_int_bus_slave.r_rdata[ID_WIDTH-1:0] = fifo_data_DP[r_ptr_SP];
      periph_int_bus_slave.r_valid = 1'b1;
      if (~fifo_empty) begin
        r_ptr_SN = (r_ptr_SP + 1) % FIFO_DEPTH;
        entry_valid_SN[r_ptr_SP] = 1'b0;
      end
    end
  end

  `ifdef SIM

  // synopsys translate_off
  // generate random data to initialize FIFO for functional rtl verification
  genvar I;
  logic [FIFO_DEPTH-1:0][ID_WIDTH-1:0] fifo_data_rand;

  generate
    for (I=0; I<FIFO_DEPTH; I++) begin
        assign fifo_data_rand[I] = $urandom_range(2**ID_WIDTH-1,0);
    end
  endgenerate
  // synopsys translate_on

  `endif

  // register setup
  always_ff @(posedge clk_i, negedge rst_ni)
  begin
    if( rst_ni == 1'b0 )
    begin
      entry_valid_SP  <= '0;
      r_ptr_SP        <= '0;
      w_ptr_SP        <= '0;
      r_req_del_SP    <= 1'b0;
      `ifdef SIM
          // synopsys translate_off
          fifo_data_DP    <= fifo_data_rand;
          // synopsys translate_on
      `else
          fifo_data_DP    <= '0;
      `endif
    end
    else
    begin
      fifo_data_DP    <= fifo_data_DN;
      entry_valid_SP  <= entry_valid_SN;
      r_ptr_SP        <= r_ptr_SN;
      w_ptr_SP        <= w_ptr_SN;
      r_req_del_SP    <= r_req_del_SN;
    end
  end

endmodule // soc_periph_fifo
