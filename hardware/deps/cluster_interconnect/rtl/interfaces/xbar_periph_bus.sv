// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

interface XBAR_PERIPH_BUS #(
  parameter int ID_WIDTH = 9  // typically number of cores plus one
);

  // Request Channel
  logic                req;
  logic         [31:0] add;
  logic                wen;
  logic         [31:0] wdata;
  logic          [3:0] be;
  logic                gnt;
  logic [ID_WIDTH-1:0] id;

  // Response Channel
  logic                r_valid;
  logic                r_opc;
  logic [ID_WIDTH-1:0] r_id;
  logic         [31:0] r_rdata;

  modport Master (
    output req, add, wen, wdata, be, id,
    input  gnt, r_rdata, r_opc, r_id, r_valid
  );

  modport Slave (
    input  req, add, wen, wdata, be, id,
    output gnt, r_rdata, r_opc, r_id, r_valid
  );

endinterface
