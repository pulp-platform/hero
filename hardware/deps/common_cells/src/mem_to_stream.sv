// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Mem-to-Stream: Allows to use memories with flow control (req/gnt) for requests but without flow
// control for output data to be used in streams.
module mem_to_stream #(
  parameter type mem_req_t = logic,
  parameter type mem_resp_t = logic,
  // Number of buffered responses (fall-through, thus no additional latency).  This defines the
  // maximum number of outstanding requests on the memory interface and must be >= 1.
  parameter int unsigned BufDepth = 1
) (
  input  logic      clk_i,
  input  logic      rst_ni,

  // Request interface
  input  mem_req_t  req_i,
  input  logic      req_valid_i,
  output logic      req_ready_o,

  // Response interface
  output mem_resp_t resp_o,
  output logic      resp_valid_o,
  input  logic      resp_ready_i,

  // Memory interface
  output mem_req_t  mem_req_o,
  output logic      mem_req_valid_o,
  input  logic      mem_req_ready_i,
  input  mem_resp_t mem_resp_i,
  input  logic      mem_resp_valid_i
);

  logic buf_ready;
  stream_fifo #(
    .FALL_THROUGH (1'b1),
    .DEPTH        (BufDepth),
    .T            (mem_resp_t)
  ) i_resp_buf (
    .clk_i,
    .rst_ni,
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     (mem_resp_i),
    .valid_i    (mem_resp_valid_i),
    .ready_o    (buf_ready),
    .data_o     (resp_o),
    .valid_o    (resp_valid_o),
    .ready_i    (resp_ready_i),
    .usage_o    (/* unused */)
  );

  assign mem_req_o = req_i;
  assign mem_req_valid_o = req_valid_i & buf_ready;
  assign req_ready_o = mem_req_ready_i & buf_ready;

  // Assertions
  `ifndef VERILATOR
  `ifndef TARGET_SYNTHESIS
    initial begin
      assert (BufDepth >= 1) else $fatal("Buffer depth must be at least 1!");
    end
  `endif
  `endif

endmodule
