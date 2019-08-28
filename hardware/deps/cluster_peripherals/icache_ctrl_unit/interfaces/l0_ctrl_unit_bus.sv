// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

interface L0_CTRL_UNIT_BUS;

  logic        flush_FetchBuffer;
  logic        flush_ack;
  logic [31:0] ctrl_stall_count;

  modport Master (
    input  ctrl_stall_count, flush_ack,
    output flush_FetchBuffer
  );

  modport Slave (
    output ctrl_stall_count, flush_ack,
    input  flush_FetchBuffer
  );

endinterface
