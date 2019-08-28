// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

interface MMU_CONFIG_BUS;

  // size of section in SRAM that is mapped in sequential
  // (non-interleaved) order for collision free private accesses,
  // always starting at the top of the whole SRAM section
  // n = 0: disable sequential section
  // n > 0: seq. section of size 2^n * 32 Byte
  logic [3:0] mmu_sram_seqsec_size;
  // seperate section can be declared sindie the SCM part
  // sizing works as above, the seq. section always starts
  // at the top of the SCM section
  logic [3:0] mmu_scm_seqsec_size;
  // NOTE: address translation can be fully disabled setting
  //       both mmu_sram_seq_size and mmu_scm_seq_size to 0
  //       (this is the default reset value)

  modport Master (
    output mmu_sram_seqsec_size, mmu_scm_seqsec_size
  );

  modport Slave (
    input mmu_sram_seqsec_size, mmu_scm_seqsec_size
  );

endinterface
