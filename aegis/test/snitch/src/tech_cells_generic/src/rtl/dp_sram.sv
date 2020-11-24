// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba    <zarubaf@iis.ee.ethz.ch>, ETH Zurich
//         Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: Dual Ported SRAM
//
module dp_sram #(
    parameter int unsigned DataWidth = 64,
    parameter int unsigned NumWords  = 1024,
    parameter bit          OutRegs   = 0,   // enables output registers in FPGA macro (read lat = 2)
    parameter logic [1:0]  SimInit   = 0    // for simulation only, will not be synthesized
                                            // 0: no init, 1: zero init, 2: random init
                                            // note: on verilator, 2 is not supported. define the VERILATOR macro to work around.
)(
   input  logic                              clk_i,
   input  logic                              rst_ni, // reset - together with the SimInit variable determines the initialization value
   input  logic [1:0]                        req_i,  // request to read or write - active high
   input  logic [1:0]                        we_i,   // write enable - active high
   input  logic [1:0][$clog2(NumWords)-1:0]  addr_i,
   input  logic [1:0][DataWidth-1:0]         wdata_i,
   input  logic [1:0][(DataWidth+7)/8-1:0]   be_i,
   output logic [1:0][DataWidth-1:0]         rdata_o,
   input  logic [1:0]                        inject_s_biterror_i, // only working for non-verilator simulation
   input  logic [1:0]                        inject_d_biterror_i
);

  mp_sram #(
    .DataWidth(DataWidth),
    .NumWords (NumWords),
    .OutRegs  (OutRegs),
    .SimInit  (SimInit),
    .NrPorts  (2)
  ) i_mp_sram (
    .clk_i
    .rst_ni
    .req_i
    .we_i
    .addr_i
    .wdata_i
    .be_i
    .rdata_o
    .inject_s_biterror_i
    .inject_d_biterror_i
  );

endmodule
