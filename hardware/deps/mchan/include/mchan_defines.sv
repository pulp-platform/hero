// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Davide Rossi <davide.rossi@unibo.it>

// MCHAN OPCODES
`define MCHAN_OP_1B     4'b0000
`define MCHAN_OP_2B     4'b0001
`define MCHAN_OP_4B     4'b0010
`define MCHAN_OP_8B     4'b0011
`define MCHAN_OP_16B    4'b0100
`define MCHAN_OP_32B    4'b0101
`define MCHAN_OP_64B    4'b0110
`define MCHAN_OP_128B   4'b0111
`define MCHAN_OP_256B   4'b1000
`define MCHAN_OP_512B   4'b1001
`define MCHAN_OP_1024B  4'b1010
`define MCHAN_OP_2048B  4'b1011
`define MCHAN_OP_4096B  4'b1100
`define MCHAN_OP_8192B  4'b1101
`define MCHAN_OP_16384B 4'b1110
`define MCHAN_OP_32768B 4'b1111

// MCHAN OPERATIONS
`define MCHAN_OP_TX 0 // TX OPERATION (FROM TCDM TO EXTERNAL MEMORY)
`define MCHAN_OP_RX 1 // RX OPERATION (FROM EXTERNAL MEMORY TO TCDM)

//MCHAN CORE INTERFACE ADDRESS SPACE
`define MCHAN_CMD_ADDR     8'h00
`define MCHAN_STATUS_ADDR  8'h04

// WIDTH OF MCHAN OPCODES
`define MCHAN_LEN_WIDTH    15
`define TWD_COUNT_WIDTH    15
`define TWD_STRIDE_WIDTH   15

`define MCHAN_OPC_WIDTH    1
`define TCDM_OPC_WIDTH     1
`define EXT_OPC_WIDTH      1