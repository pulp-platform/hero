// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`ifndef MUT_IMPL
  `define MUT_IMPL 2
 `endif
`ifndef NUM_MASTER
  `define NUM_MASTER 16
 `endif
`ifndef BANK_FACT
  `define BANK_FACT 2
 `endif
`ifndef DATA_WIDTH
  `define DATA_WIDTH 32
`endif
`ifndef TCDM_SIZE
  `define TCDM_SIZE 128*1024
`endif
`ifndef MEM_ADDR_BITS
  `define MEM_ADDR_BITS $clog2(`TCDM_SIZE/`NUM_MASTER/`BANK_FACT)
`endif
`ifndef PAR_STAGES
  `define PAR_STAGES 1
`endif
`ifndef TEST_CYCLES
  // scale this with the number of master ports (= bins)
  // for reliable statistics
  `define TEST_CYCLES (150*`NUM_MASTER)
`endif
