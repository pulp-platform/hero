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

module trans_unit
  #(
    parameter MCHAN_LEN_WIDTH = 15
    )
   (
    
    input  logic                       clk_i,
    input  logic                       rst_ni,
    
    // TX CTRL INTERFACE
    input  logic                       tx_trans_req_i,
    output logic                       tx_trans_gnt_o,
    input  logic [2:0]                 tx_trans_ext_addr_i,
    input  logic [2:0]                 tx_trans_tcdm_addr_i,
    input  logic [MCHAN_LEN_WIDTH-1:0] tx_trans_len_i,
    
    // RX CTRL INTERFACE
    input  logic                       rx_trans_req_i,
    output logic                       rx_trans_gnt_o,
    input  logic [2:0]                 rx_trans_tcdm_addr_i,
    input  logic [2:0]                 rx_trans_ext_addr_i,
    input  logic [MCHAN_LEN_WIDTH-1:0] rx_trans_len_i,
    
    // TCDM SIDE
    input  logic [1:0][31:0]           tx_data_push_dat_i,
    input  logic [1:0]                 tx_data_push_req_i,
    output logic [1:0]                 tx_data_push_gnt_o,
    
    // TCDM SIDE
    output logic [1:0][31:0]           rx_data_pop_dat_o,
    output logic [1:0][3:0]            rx_data_pop_strb_o,
    input  logic [1:0]                 rx_data_pop_req_i,
    output logic [1:0]                 rx_data_pop_gnt_o,
    
    // EXT SIDE
    output logic [63:0]                tx_data_pop_dat_o,
    output logic [7:0]                 tx_data_pop_strb_o,
    input  logic                       tx_data_pop_req_i,
    output logic                       tx_data_pop_gnt_o,
    
    // EXT SIDE
    input  logic [63:0]                rx_data_push_dat_i,
    input  logic                       rx_data_push_req_i,
    output logic                       rx_data_push_gnt_o
    
    );
   
   logic [63:0] 		       s_rx_data_ext_dat,s_rx_data_tcdm_dat,s_tx_data_ext_dat,s_tx_data_tcdm_dat;
   logic [7:0] 			       s_rx_data_tcdm_strb,s_tx_data_ext_strb;
   logic  			       s_rx_data_ext_req,s_rx_data_tcdm_req,s_tx_data_ext_req,s_tx_data_tcdm_req;
   logic  			       s_rx_data_ext_gnt,s_rx_data_tcdm_gnt,s_tx_data_ext_gnt,s_tx_data_tcdm_gnt;
   
   logic [MCHAN_LEN_WIDTH-1:0] 	       s_tx_trans_len,s_rx_trans_len;
   logic [2:0] 			       s_tx_trans_tcdm_addr,s_rx_trans_tcdm_addr;
   logic [2:0] 			       s_tx_trans_ext_addr,s_rx_trans_ext_addr;
   logic 			       s_tx_trans_req,s_rx_trans_req;
   logic 			       s_tx_trans_gnt,s_rx_trans_gnt;
   
   //*****************************************************************
   //** TRANS BUFFERS TCDM SIDE: DECOUPLE TCDM IF AND TRANS ALIGNER **
   //*****************************************************************
   
   trans_buffers
     #(
       .RX_BUFFER_DEPTH(2),
       .TX_BUFFER_DEPTH(2)
       )
   trans_buffers_tcdm_i
     (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .tx_data_push_dat_i(tx_data_push_dat_i),
      .tx_data_push_req_i(tx_data_push_req_i),
      .tx_data_push_gnt_o(tx_data_push_gnt_o),
      
      .rx_data_pop_dat_o(rx_data_pop_dat_o),
      .rx_data_pop_strb_o(rx_data_pop_strb_o),
      .rx_data_pop_req_i(rx_data_pop_req_i),
      .rx_data_pop_gnt_o(rx_data_pop_gnt_o),
      
      .tx_data_pop_dat_o(s_tx_data_tcdm_dat),
      .tx_data_pop_req_i(s_tx_data_tcdm_gnt),
      .tx_data_pop_gnt_o(s_tx_data_tcdm_req),
      
      .rx_data_push_dat_i(s_rx_data_tcdm_dat),
      .rx_data_push_strb_i(s_rx_data_tcdm_strb),
      .rx_data_push_req_i(s_rx_data_tcdm_gnt),
      .rx_data_push_gnt_o(s_rx_data_tcdm_req)
      );
   
   //****************************************************************
   //** TRANS BUFFERS EXT SIDE: DECOUPLE AXI IF AND TRANS ALIGNERS **
   //****************************************************************
   
   mchan_fifo
     #(
       .DATA_WIDTH(72),
       .DATA_DEPTH(2)
       )
   trans_buffer_ext_tx_i
     (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .push_dat_i({s_tx_data_ext_strb,s_tx_data_ext_dat}),
      .push_req_i(s_tx_data_ext_gnt),
      .push_gnt_o(s_tx_data_ext_req),
      
      .pop_dat_o({tx_data_pop_strb_o,tx_data_pop_dat_o}),
      .pop_req_i(tx_data_pop_req_i),
      .pop_gnt_o(tx_data_pop_gnt_o)
      );
   
   mchan_fifo
     #(
       .DATA_WIDTH(64),
       .DATA_DEPTH(2)
       )
   trans_buffer_ext_rx_i
     (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .push_dat_i(rx_data_push_dat_i),
      .push_req_i(rx_data_push_req_i),
      .push_gnt_o(rx_data_push_gnt_o),
      
      .pop_dat_o(s_rx_data_ext_dat),
      .pop_req_i(s_rx_data_ext_gnt),
      .pop_gnt_o(s_rx_data_ext_req)
      );
   
   //**********************************************************
   //** TRANS QUEUES: DECOUPLE CMD UNPACK AND TRANS ALIGNERS **
   //**********************************************************
   
   mchan_fifo
     #(
       .DATA_WIDTH(MCHAN_LEN_WIDTH+6),
       .DATA_DEPTH(2)
       )
   trans_queue_tx_i
     (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .push_dat_i({tx_trans_len_i,tx_trans_tcdm_addr_i,tx_trans_ext_addr_i}),
      .push_req_i(tx_trans_req_i),
      .push_gnt_o(tx_trans_gnt_o),
      
      .pop_dat_o({s_tx_trans_len,s_tx_trans_tcdm_addr,s_tx_trans_ext_addr}),
      .pop_req_i(s_tx_trans_gnt),
      .pop_gnt_o(s_tx_trans_req)
      );
   
   mchan_fifo
     #(
       .DATA_WIDTH(MCHAN_LEN_WIDTH+6),
       .DATA_DEPTH(2)
       )
   trans_queue_rx_i
     (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .push_dat_i({rx_trans_len_i,rx_trans_tcdm_addr_i,rx_trans_ext_addr_i}),
      .push_req_i(rx_trans_req_i),
      .push_gnt_o(rx_trans_gnt_o),
      
      .pop_dat_o({s_rx_trans_len,s_rx_trans_tcdm_addr,s_rx_trans_ext_addr}),
      .pop_req_i(s_rx_trans_gnt),
      .pop_gnt_o(s_rx_trans_req)
      );
   
   //********************************************************************
   //** TRANS ALIGNERS: MANAGE UNALINGED TRANSFERS IN TCDM AND EXT IFs **
   //********************************************************************
   
   trans_aligner
     #(
       .MCHAN_LEN_WIDTH(MCHAN_LEN_WIDTH)
       )
   trans_aligner_tx_i
     (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .trans_req_i(s_tx_trans_req),
      .trans_gnt_o(s_tx_trans_gnt),
      .trans_pop_addr_i(s_tx_trans_ext_addr),
      .trans_push_addr_i(s_tx_trans_tcdm_addr),
      .trans_len_i(s_tx_trans_len),
      
      .data_pop_dat_o(s_tx_data_ext_dat),
      .data_pop_strb_o(s_tx_data_ext_strb),
      .data_pop_req_i(s_tx_data_ext_req),
      .data_pop_gnt_o(s_tx_data_ext_gnt),
      
      .data_push_dat_i(s_tx_data_tcdm_dat),
      .data_push_req_i(s_tx_data_tcdm_req),
      .data_push_gnt_o(s_tx_data_tcdm_gnt)
      );
   
   trans_aligner
     #(
       .MCHAN_LEN_WIDTH(MCHAN_LEN_WIDTH)
       )
   trans_aligner_rx_i
     (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .trans_req_i(s_rx_trans_req),
      .trans_gnt_o(s_rx_trans_gnt),
      .trans_pop_addr_i(s_rx_trans_tcdm_addr),
      .trans_push_addr_i(s_rx_trans_ext_addr),
      .trans_len_i(s_rx_trans_len),
      
      .data_pop_dat_o(s_rx_data_tcdm_dat),
      .data_pop_strb_o(s_rx_data_tcdm_strb),
      .data_pop_req_i(s_rx_data_tcdm_req),
      .data_pop_gnt_o(s_rx_data_tcdm_gnt),
      
      .data_push_dat_i(s_rx_data_ext_dat),
      .data_push_req_i(s_rx_data_ext_req),
      .data_push_gnt_o(s_rx_data_ext_gnt)
      );
     
endmodule
