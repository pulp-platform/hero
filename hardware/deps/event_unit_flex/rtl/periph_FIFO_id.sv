/*
 * Copyright (C) 2013-2017 ETH Zurich, University of Bologna
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
 
module periph_FIFO_id
#(
    parameter ADDR_WIDTH=32,
    parameter DATA_WIDTH=32,
    parameter ID_WIDTH=8,
    parameter BYTE_ENABLE_BIT=DATA_WIDTH/8
)
(
    input  logic			 clk_i,
    input  logic			 rst_ni,
    input  logic       test_en_i,

    //Input SIde REQ
    input  logic 			 data_req_i,
    input  logic [ADDR_WIDTH - 1:0] 	 data_add_i,
    input  logic 			 data_wen_i,
    input  logic [DATA_WIDTH - 1:0] 	 data_wdata_i,
    input  logic [BYTE_ENABLE_BIT - 1:0] data_be_i,
    input  logic [ID_WIDTH - 1:0] data_id_i,
    output logic 			 data_gnt_o,

    //Output side REQ
    output logic 			 data_req_o,
    output logic [ADDR_WIDTH - 1:0] 	 data_add_o,
    output logic 			 data_wen_o,
    output logic [DATA_WIDTH - 1:0] 	 data_wdata_o,
    output logic [BYTE_ENABLE_BIT - 1:0] data_be_o,
    output logic [ID_WIDTH - 1:0] data_id_o,
    input logic 			 data_gnt_i,

    //Input SIde RESP
    input logic 			 data_r_valid_i,
    input logic 			 data_r_opc_i,
    input logic [ID_WIDTH - 1:0] data_r_id_i,
    input logic [DATA_WIDTH - 1:0] 	 data_r_rdata_i,

    //Output SIde RESP
    output logic 			 data_r_valid_o,
    output logic 			 data_r_opc_o,
    output logic [ID_WIDTH - 1:0] data_r_id_o,
    output logic [DATA_WIDTH - 1:0] 	 data_r_rdata_o
);

localparam FIFO_DW = ADDR_WIDTH + 1 + DATA_WIDTH + ID_WIDTH + BYTE_ENABLE_BIT;

logic [FIFO_DW-1:0]	DATA_IN;
logic [FIFO_DW-1:0]	DATA_OUT;

assign DATA_IN  = { data_add_i, data_wen_i, data_wdata_i, data_id_i, data_be_i };
assign            { data_add_o, data_wen_o, data_wdata_o, data_id_o, data_be_o } = DATA_OUT;



generic_fifo
#( 
      .DATA_WIDTH ( FIFO_DW   ),
      .DATA_DEPTH ( 2         )
)
FIFO_REQ
(
      .clk          ( clk_i      ),
      .rst_n        ( rst_ni     ),
      .test_mode_i  ( test_en_i  ),
      .data_i       ( DATA_IN    ),
      .valid_i      ( data_req_i ),
      .grant_o      ( data_gnt_o ),
      .data_o       ( DATA_OUT   ),
      .valid_o      ( data_req_o ),
      .grant_i      ( data_gnt_i )
);

// response channel is forwarded (no FIFO)
assign data_r_valid_o = data_r_valid_i;
assign data_r_opc_o   = data_r_opc_i;
assign data_r_id_o    = data_r_id_i;
assign data_r_rdata_o = data_r_rdata_i;



endmodule