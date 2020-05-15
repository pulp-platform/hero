// Copyright (c) 2014-2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Andreas Kurth <akurth@iis.ee.ethz.ch>
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

module axi_id_remap_table #(
  parameter int unsigned ID_WIDTH_INP = 0,
  // Maximum number of AXI read and write bursts outstanding at the same time
  parameter int unsigned MAX_TXNS = 0,
  // Derived Parameters (do NOT change manually!)
  parameter type field_t = logic [MAX_TXNS-1:0],
  parameter type id_inp_t = logic [ID_WIDTH_INP-1:0],
  parameter int unsigned IDX_WIDTH = $clog2(MAX_TXNS) > 0 ? $clog2(MAX_TXNS) : 1,
  parameter type idx_t = logic [IDX_WIDTH-1:0]
) (
  input  logic    clk_i,
  input  logic    rst_ni,

  output field_t  free_o,
  output idx_t    free_oup_id_o,
  output logic    full_o,

  input  id_inp_t push_inp_id_i,
  input  idx_t    push_oup_id_i,
  input  logic    push_i,

  input  id_inp_t exists_inp_id_i,
  output idx_t    exists_oup_id_o,
  output logic    exists_full_o,
  output logic    exists_o,

  input  idx_t    pop_oup_id_i,
  output id_inp_t pop_inp_id_o,
  input  logic    pop_i
);

  localparam int unsigned CNT_WIDTH = $clog2(MAX_TXNS+1);
  typedef logic [CNT_WIDTH-1:0] cnt_t;

  typedef struct packed {
    id_inp_t  inp_id;
    cnt_t     cnt;    // number of in-flight bursts with that ID
  } entry_t;

  // Table indexed by output IDs that contains the corresponding input IDs
  entry_t [MAX_TXNS-1:0] table_d, table_q;

  // Determine lowest free output ID.
  for (genvar i = 0; i < MAX_TXNS; i++) begin : gen_free_o
    assign free_o[i] = table_q[i].cnt == '0;
  end
  lzc #(
    .WIDTH    (MAX_TXNS),
    .MODE     (1'b0)
  ) i_lzc_free (
    .in_i     (free_o),
    .cnt_o    (free_oup_id_o),
    .empty_o  (full_o)
  );

  // Determine the input ID for a given output ID.
  assign pop_inp_id_o = table_q[pop_oup_id_i].inp_id;

  // Determine if given output ID is already used and, if it is, by which input ID.
  field_t match;
  for (genvar i = 0; i < MAX_TXNS; i++) begin : gen_match
    assign match[i] = table_q[i].cnt > 0 && table_q[i].inp_id == exists_inp_id_i;
  end
  logic no_match;
  lzc #(
      .WIDTH    (MAX_TXNS),
      .MODE     (1'b0)
  ) i_lzc_match (
      .in_i     (match),
      .cnt_o    (exists_oup_id_o),
      .empty_o  (no_match)
  );
  assign exists_o = ~no_match;
  assign exists_full_o = table_q[exists_oup_id_o].cnt == MAX_TXNS;

  // Push and pop table entries.
  always_comb begin
    table_d = table_q;
    if (push_i) begin
      table_d[push_oup_id_i].inp_id = push_inp_id_i;
      table_d[push_oup_id_i].cnt += 1;
    end
    if (pop_i) begin
      table_d[pop_oup_id_i].cnt -= 1;
    end
  end

  // Registers
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      table_q <= '0;
    end else begin
      table_q <= table_d;
    end
  end

  // Assertions
  `ifndef TARGET_SYNTHESIS
    default disable iff (!rst_ni);
    assume property (@(posedge clk_i) push_i |->
        table_q[push_oup_id_i].cnt == '0 || table_q[push_oup_id_i].inp_id == push_inp_id_i)
      else $error("Push must be to empty output ID or match existing input ID!");
    assume property (@(posedge clk_i) push_i |-> table_q[push_oup_id_i].cnt < MAX_TXNS)
      else $error("Maximum number of in-flight bursts must not be exceeded!");
    assume property (@(posedge clk_i) pop_i |-> table_q[pop_oup_id_i].cnt > 0)
      else $error("Pop must target output ID with non-zero counter!");
    assume property (@(posedge clk_i) $onehot0(match))
      else $error("Input ID in table must be unique!");
    initial begin
      assert (ID_WIDTH_INP > 0);
      assert (MAX_TXNS > 0);
      assert (IDX_WIDTH >= 1);
    end
  `endif

endmodule
