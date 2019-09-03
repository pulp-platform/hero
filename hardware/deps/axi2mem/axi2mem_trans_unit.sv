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

module axi2mem_trans_unit
#(
    parameter LD_BUFFER_SIZE = 2,
    parameter ST_BUFFER_SIZE = 2
)
(
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             test_en_i,

    // TCDM SIDE
    input  logic [1:0][31:0] rd_data_push_dat_i,
    input  logic [1:0]       rd_data_push_req_i,
    output logic [1:0]       rd_data_push_gnt_o,
    input  logic [5:0]       rd_data_push_id_i,
    input  logic             rd_data_push_last_i,

    // EXT SIDE
    output logic [63:0]      rd_data_pop_dat_o,
    input  logic             rd_data_pop_req_i,
    output logic             rd_data_pop_gnt_o,
    output logic [5:0]       rd_data_pop_id_o,
    output logic             rd_data_pop_last_o,

    // EXT SIDE
    input  logic [63:0]      wr_data_push_dat_i,
    input  logic [7:0]       wr_data_push_strb_i,
    input  logic             wr_data_push_req_i,
    output logic             wr_data_push_gnt_o,

    // TCDM SIDE
    output logic [1:0][31:0] wr_data_pop_dat_o,
    output logic [1:0][3:0]  wr_data_pop_strb_o,
    input  logic [1:0]       wr_data_pop_req_i,
    output logic [1:0]       wr_data_pop_gnt_o
);

   logic [1:0][31:0]         s_rd_data_pop_dat;
   logic [1:0]               s_rd_data_pop_req;
   logic [1:0]               s_rd_data_pop_gnt;

   logic [1:0][31:0]         s_wr_data_push_dat;
   logic [1:0][3:0]          s_wr_data_push_strb;
   logic [1:0]               s_wr_data_push_req;
   logic [1:0]               s_wr_data_push_gnt;

   logic                     s_rd_last_pop_req;
   logic                     s_rd_last_pop_gnt;
   genvar                    i;

   //**********************************************************
   //*************** RD LAST BUFFER ***************************
   //**********************************************************
   generic_fifo
   #(
       .DATA_WIDTH(1),
       .DATA_DEPTH(LD_BUFFER_SIZE)
   )
   last_buffer_i
   (
      .clk           ( clk_i                  ),
      .rst_n         ( rst_ni                 ),
      .test_mode_i   ( test_en_i              ),
    
      .data_i        ( rd_data_push_last_i    ),
      .valid_i       ( rd_data_push_req_i[0]  ),
      .grant_o       (                        ),

      .data_o        ( rd_data_pop_last_o     ),
      .grant_i       ( s_rd_last_pop_req      ),
      .valid_o       ( s_rd_last_pop_gnt      )
   );


   //**********************************************************
   //*************** RD BUFFER ********************************
   //**********************************************************

   generate

      for (i=0; i<2; i++)
      begin : rd_buffer

           generic_fifo
           #(
               .DATA_WIDTH(32),
               .DATA_DEPTH(LD_BUFFER_SIZE)
           )
           rd_buffer_i
           (
              .clk(clk_i),
              .rst_n(rst_ni),
              .test_mode_i(test_en_i),

              .data_i(rd_data_push_dat_i[i]),
              .valid_i(rd_data_push_req_i[i]),
              .grant_o(rd_data_push_gnt_o[i]),

              .data_o(s_rd_data_pop_dat[i]),
              .grant_i(s_rd_data_pop_req[i]),
              .valid_o(s_rd_data_pop_gnt[i])
           );
      end

   endgenerate

   //**********************************************************
   //*************** WR BUFFER ********************************
   //**********************************************************

   generate

      for (i=0; i<2; i++)
      begin : wr_buffer
           generic_fifo
           #(
               .DATA_WIDTH(36),
               .DATA_DEPTH(ST_BUFFER_SIZE)
           )
           wr_buffer_i
           (
              .clk(clk_i),
              .rst_n(rst_ni),
              .test_mode_i(test_en_i),

              .data_i({s_wr_data_push_strb[i],s_wr_data_push_dat[i]}),
              .valid_i(s_wr_data_push_req[i]),
              .grant_o(s_wr_data_push_gnt[i]),

              .data_o({wr_data_pop_strb_o[i],wr_data_pop_dat_o[i]}),
              .grant_i(wr_data_pop_req_i[i]),
              .valid_o(wr_data_pop_gnt_o[i])
           );
      end

   endgenerate

   // REAL SIGNALS
   assign rd_data_pop_gnt_o        = s_rd_data_pop_gnt[0] & s_rd_data_pop_gnt[1] & s_rd_last_pop_gnt;
   assign wr_data_push_gnt_o       = s_wr_data_push_gnt[0] & s_wr_data_push_gnt[1];
   assign s_rd_data_pop_req[0]     = rd_data_pop_req_i;
   assign s_rd_data_pop_req[1]     = rd_data_pop_req_i;
   assign s_rd_last_pop_req        = rd_data_pop_req_i;
   assign s_wr_data_push_req[0]    = wr_data_push_req_i;
   assign s_wr_data_push_req[1]    = wr_data_push_req_i;
   assign rd_data_pop_dat_o[31:0]  = s_rd_data_pop_dat[0];
   assign rd_data_pop_dat_o[63:32] = s_rd_data_pop_dat[1];
   assign s_wr_data_push_dat[0]    = wr_data_push_dat_i[31:0];
   assign s_wr_data_push_dat[1]    = wr_data_push_dat_i[63:32];
   assign s_wr_data_push_strb[0]   = wr_data_push_strb_i[3:0];
   assign s_wr_data_push_strb[1]   = wr_data_push_strb_i[7:4];

endmodule
