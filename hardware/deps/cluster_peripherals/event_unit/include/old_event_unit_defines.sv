// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// 0x00 = TCDM bank 0
// 0x04 = TCDM bank 1
// 0x08 = TCDM bank 2
// 0x0c = TCDM bank 3
// 0x10 = CORE 0 NOT USED
// 0x14 = CORE 1 NOT USED
// 0x18 = CORE 2 NOT USED
// 0x1c = CORE 3 NOT USED
// 0x20 = Cluster Internal 0
// 0x24 = SCM 0
// 0X28 = BBMUX_SEL
//`define FEATURE_IDLE_CNT     // IT ENABLES AN IDLE CYCLES COUNTER INSIDE THE STATE MACHINE
`define FEATURE_DEMUX_MAPPED   // SLEEP REQUEST AND CLEAR EVENT BUFFER OPERATION MAPPED DIRECTLY TO THE DEMUX..SAVES INTERCONNECT LATENCY
`define EVENT_BIT    8
`define IRQ_BIT      9
`define CMP_LOW_BIT  2
`define CMP_HIGH_BIT 7
`define NUM_BARRIERS 6
`define GP_EVNT      3

//////////////                \\\\\\\\\\\\\\\\
//////          BODY BIASING        \\\\\\\\\\
/////////////                  \\\\\\\\\\\\\\\

`define BB_TCDM0         6'h0 //0X1022_0000
`define BB_TCDM1         6'h1 //0X1022_0004
`define BB_TCDM2         6'h2 //0X1022_0008
`define BB_TCDM3         6'h3 //0X1022_000C
`define BB_SCM           6'h4 //0X1022_0010
`define BB_CLUSTER       6'h5 //0X1022_0014
`define BB_CORE_BASE     6'h6 //0X1022_0018
`define BBMUX_SEL        6'h16 //0X1022_0058

//////////////
////////////	EVENT MASK
/////////////

`define	EV_MASK_LOW_BASE  6'h0//0X1022_0100
`define EV_MASK_HIGH_BASE 6'h10 //0X1022_0140
//////////////
/////////////	EVENT BUFFERS
//////////////

`define	EV_BUFFER_LOW_BASE    6'h20//0X1022_0180
`define EV_BUFFER_HIGH_BASE   6'h30 //0X1022_01C0
////////////
//////////	INTERRUPTS MASK
////////////


`define IRQ_MASK_LOW_BASE  6'h0 //0X1022_0200
`define IRQ_MASK_HIGH_BASE 6'h10 //0X1022_0240
////////////
//////////	INTERRUPT BUFFERS
////////////

`define IRQ_BUFFER_LOW_BASE  6'h20 //0X1022_0280
`define IRQ_BUFFER_HIGH_BASE 6'h30 //0X1022_02C0

`define CLKGATE_SET            6'h0 //0X1022_0300 //clockgate tcdm,sram, cluster region
`define CLKGATE_CLEAR          6'h1 //0X1022_0304
`define CORE_CLKGATE           6'h2 //0X1022_0308 //clockgate core
`define EMERGENCY_EVENT_SET    6'h3 //0X1022_030C
`define EMERGENCY_IRQ_SET      6'h4 //0X1022_0310
`define EMERGENCY_EVENT_CLEAR  6'h5 //0X1022_0314
`define EMERGENCY_IRQ_CLEAR    6'h6 //0X1022_0318
`define READ_IRQ_ID_BASE       6'h7 //0X1022_031C
//NEXT FREE ADDR 0X1022_035C
`define TRIGG_BARRIER          6'h17 //0X1022_035C
`define GP_0                   6'h18 //0X1022_0360
`define GP_1                   6'h19 //0X1022_0364
`define GP_2                   6'h1A //0X1022_0368
`define WAIT_BARRIER           6'h1B //0X1022_036C
`define CLEAR_BARRIER          6'h1C //0X1022_0370
`define SET_BARRIER_BASE       6'h1D //0X1022_0374
`ifdef FEATURE_IDLE_CNT
  `define CLEAR_IDLE_CNT       6'h23 //0X1022_038C // one for each core
  `define IDLE_CYC_CNT_BASE    6'h24 //0X1022_0390 // one for each core
`endif
//NEXT FREE ADDR 0X1022_039C
