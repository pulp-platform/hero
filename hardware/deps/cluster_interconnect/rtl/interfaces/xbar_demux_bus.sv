// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

interface XBAR_DEMUX_BUS;

  // Request Channel
  logic        barrier;
  logic        busy;
  logic        exec_cancel;
  logic        exec_stall;
  logic        req;
  logic [31:0] add;
  logic        we;
  logic  [5:0] atop;
  logic [31:0] wdata;
  logic  [3:0] be;
  logic        gnt;

  // Response Channel
  logic        r_gnt;
  logic        r_valid;
  logic [31:0] r_rdata;

  modport Master (
    output barrier, exec_cancel, exec_stall, req, add, we, atop, wdata, be, r_gnt,
    input  busy, gnt, r_rdata, r_valid
  );

  modport Slave (
    input  barrier, exec_cancel, exec_stall, req, add, we, atop, wdata, be, r_gnt,
    output busy, gnt, r_rdata, r_valid
  );

endinterface
