// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

interface MP_ICACHE_CTRL_UNIT_BUS #(
  parameter int NB_CORES = 4
);

  logic                       bypass_req;
  logic    [NB_CORES:0]       bypass_ack; // NB_CORES + 1
  logic                       flush_req;
  logic                       flush_ack;

  logic                       sel_flush_req;
  logic                [31:0] sel_flush_addr;
  logic                       sel_flush_ack;
  logic                [31:0] global_hit_count;
  logic                [31:0] global_trans_count;
  logic                [31:0] global_miss_count;

  logic  [NB_CORES-1:0][31:0] bank_hit_count;
  logic  [NB_CORES-1:0][31:0] bank_trans_count;
  logic  [NB_CORES-1:0][31:0] bank_miss_count;

  logic                       ctrl_clear_regs;
  logic                       ctrl_enable_regs;

  modport Master (
    output bypass_req, flush_req, sel_flush_req, sel_flush_addr, ctrl_clear_regs, ctrl_enable_regs,
    input  bypass_ack, flush_ack, sel_flush_ack, global_hit_count, global_trans_count,
           global_miss_count, bank_hit_count, bank_trans_count, bank_miss_count
  );

  modport Slave (
    input  bypass_req, flush_req, sel_flush_req, sel_flush_addr, ctrl_clear_regs, ctrl_enable_regs,
    output bypass_ack, flush_ack, sel_flush_ack, global_hit_count, global_trans_count,
           global_miss_count, bank_hit_count, bank_trans_count, bank_miss_count
  );

endinterface
