/* Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 *
 * This code is under development and not yet released to the public.
 * Until it is released, the code is under the copyright of ETH Zurich and
 * the University of Bologna, and may contain confidential and/or unpublished
 * work. Any reuse/redistribution is strictly forbidden without written
 * permission from ETH Zurich.
 *
 * Bug fixes and contributions will eventually be released under the
 * SolderPad open hardware license in the context of the PULP platform
 * (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
 * University of Bologna.
 */


`ifndef GF_TRACK
  `define GF_TRACK  8
`endif

`ifndef GF_VT
  `define GF_VT     L
`endif

`ifndef GF_LEN
  `define GF_LEN   24
`endif

//andy hack: support different standard cell libraries by setting `GF_TRACK,
//`GF_VT and `GF_LEN
// SC8T_CKGPRELATNX1_CSC24L
`define GF_PREICG(t,v,c)  SC``t``T_CKXOR2X4_CSC``c``v

module pulp_clock_xor2
(
   input  logic clk0_i,
   input  logic clk1_i,
   output logic clk_o
);

  `GF_PREICG(`GF_TRACK, `GF_VT, `GF_LEN) clk_xor_i
   (
      .Z(clk_o),
      .CLK(clk0_i),
      .EN(clk1_i) 
   );

endmodule


