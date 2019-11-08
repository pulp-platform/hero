// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Stream join: Joins a parametrizable number of input streams (i.e., valid-ready handshaking with
// dependency rules as in AXI4) to a single output stream.  The output handshake happens only once
// all inputs are valid.  The data channel flows outside of this module.

module stream_join #(
    parameter int unsigned N_INP = 0  // Synopsys DC requires a default value for parameters.
) (
    input  logic  [N_INP-1:0] inp_valid_i,
    output logic  [N_INP-1:0] inp_ready_o,

    output logic              oup_valid_o,
    input  logic              oup_ready_i
);

  assign oup_valid_o = (&inp_valid_i);
  for (genvar i = 0; i < N_INP; i++) begin : gen_inp_ready
    assign inp_ready_o[i] = oup_valid_o & oup_ready_i;
  end

  `ifndef TARGET_SYNTHESIS
  `ifndef VERILATOR
    initial begin
      assert (N_INP > 0) else $fatal("There must be at least one input!");
    end
  `endif
  `endif

endmodule
