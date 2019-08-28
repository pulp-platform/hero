// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

interface SP_ICACHE_CTRL_UNIT_BUS;

  logic        ctrl_req_enable;
  logic        ctrl_ack_enable;
  logic        ctrl_req_disable;
  logic        ctrl_ack_disable;
  logic        ctrl_pending_trans;
  logic        flush_req;
  logic        flush_ack;
  logic        icache_is_private;
  logic [31:0] ctrl_hit_count;
  logic [31:0] ctrl_trans_count;
  logic [31:0] ctrl_miss_count;
  logic        ctrl_clear_regs;
  logic        ctrl_enable_regs;

  modport Master (
    output  ctrl_req_enable, ctrl_req_disable, flush_req, icache_is_private, ctrl_clear_regs,
            ctrl_enable_regs,
    input   flush_ack, ctrl_ack_enable, ctrl_ack_disable, ctrl_pending_trans, ctrl_hit_count,
            ctrl_trans_count, ctrl_miss_count
  );

  modport Slave (
    input   ctrl_req_enable, ctrl_req_disable, flush_req, icache_is_private, ctrl_clear_regs,
            ctrl_enable_regs,
    output  flush_ack, ctrl_ack_enable, ctrl_ack_disable, ctrl_pending_trans, ctrl_hit_count,
            ctrl_trans_count, ctrl_miss_count
  );

endinterface
