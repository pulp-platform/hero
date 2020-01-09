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

`include "mchan_defines.sv"

module ctrl_if
  #(
    // OVERRIDDEN FROM TOP
    parameter NB_TRANSFERS           = 4,
    parameter TWD_QUEUE_DEPTH        = 4,
    parameter CTRL_TRANS_QUEUE_DEPTH = 2,
    parameter TCDM_ADD_WIDTH         = 12,
    parameter EXT_ADD_WIDTH          = 29,
    parameter TWD_COUNT_WIDTH        = 16,
    parameter TWD_STRIDE_WIDTH       = 16,
    parameter TWD_QUEUE_WIDTH        = TWD_STRIDE_WIDTH+TWD_COUNT_WIDTH,
    parameter PE_ID_WIDTH            = 1,
    // DEFINED IN MCHAN_DEFINES
    parameter MCHAN_OPC_WIDTH        = `MCHAN_OPC_WIDTH,
    parameter MCHAN_LEN_WIDTH        = `MCHAN_LEN_WIDTH,
    parameter TWD_QUEUE_ADD_WIDTH    = (TWD_QUEUE_DEPTH == 1) ? 1 : $clog2(TWD_QUEUE_DEPTH),
    parameter TRANS_SID_WIDTH        = (NB_TRANSFERS == 1) ? 1 : $clog2(NB_TRANSFERS)
    )
   (
    
    input logic 			   clk_i,
    input logic 			   rst_ni,
    
    input logic 			   test_mode_i,
    
    // CONTROL TARGET
    //***************************************
    input logic 			   ctrl_targ_req_i,
    input logic 			   ctrl_targ_type_i,
    input logic [3:0] 			   ctrl_targ_be_i,
    input logic [31:0] 			   ctrl_targ_add_i,
    input logic [31:0] 			   ctrl_targ_data_i,
    input logic [PE_ID_WIDTH-1:0] 	   ctrl_targ_id_i,
    output logic 			   ctrl_targ_gnt_o,
    
    output logic 			   ctrl_targ_r_valid_o,
    output logic [31:0] 		   ctrl_targ_r_data_o,
    output logic 			   ctrl_targ_r_opc_o,
    output logic [PE_ID_WIDTH-1:0] 	   ctrl_targ_r_id_o,
    
    // TRANSFERS ALLCOATOR INTERFACE
    //***************************************
    // RETRIVE SID SIGNALS
    output logic 			   trans_alloc_req_o,
    input logic 			   trans_alloc_gnt_i,
    input logic [TRANS_SID_WIDTH-1:0] 	   trans_alloc_ret_i,
    // CLEAR SID SIGNALS
    output logic [NB_TRANSFERS-1:0] 	   trans_alloc_clr_o,
    // STATUS SIGNALS
    input logic [NB_TRANSFERS-1:0] 	   trans_alloc_status_i,
    
    // CMD QUEUE INTERFACE
    //***************************************
    output logic 			   cmd_req_o,
    input logic 			   cmd_gnt_i,
    output logic [MCHAN_LEN_WIDTH-1:0] 	   cmd_len_o,
    output logic [MCHAN_OPC_WIDTH-1:0] 	   cmd_opc_o,
    output logic 			   cmd_inc_o,
    output logic 			   cmd_twd_ext_o,
    output logic 			   cmd_ele_o,
    output logic 			   cmd_ile_o,
    output logic 			   cmd_ble_o,
    output logic 			   cmd_twd_tcdm_o,
    output logic [TWD_QUEUE_ADD_WIDTH-1:0] cmd_twd_ext_add_o,
    output logic [TWD_QUEUE_ADD_WIDTH-1:0] cmd_twd_tcdm_add_o,
    output logic [TRANS_SID_WIDTH-1:0] 	   cmd_sid_o,
    output logic [TCDM_ADD_WIDTH-1:0] 	   tcdm_add_o,
    output logic [EXT_ADD_WIDTH-1:0] 	   ext_add_o,
    
    output logic 			   twd_ext_alloc_req_o,
    input logic 			   twd_ext_alloc_gnt_i,
    input logic [TWD_QUEUE_ADD_WIDTH-1:0]  twd_ext_alloc_add_i,
    
    output logic 			   twd_ext_queue_req_o,
    output logic [TWD_QUEUE_ADD_WIDTH-1:0] twd_ext_queue_add_o,
    output logic [TWD_QUEUE_WIDTH-1:0] 	   twd_ext_queue_dat_o,
    output logic [TRANS_SID_WIDTH-1:0] 	   twd_ext_queue_sid_o,
    
    output logic 			   twd_tcdm_alloc_req_o,
    input logic 			   twd_tcdm_alloc_gnt_i,
    input logic [TWD_QUEUE_ADD_WIDTH-1:0]  twd_tcdm_alloc_add_i,
    
    output logic 			   twd_tcdm_queue_req_o,
    output logic [TWD_QUEUE_ADD_WIDTH-1:0] twd_tcdm_queue_add_o,
    output logic [TWD_QUEUE_WIDTH-1:0] 	   twd_tcdm_queue_dat_o,
    output logic [TRANS_SID_WIDTH-1:0] 	   twd_tcdm_queue_sid_o,
    
    // SYNCH UNIT INTERFACE
    //***************************************
    input logic 			   arb_gnt_i,
    input logic 			   arb_req_i,
    input logic [TRANS_SID_WIDTH-1:0] 	   arb_sid_i,
    
    // SYNCHRONIZATION INTERFACE
    //***************************************
    input logic [NB_TRANSFERS-1:0] 	   trans_status_i,
    
    // BUSY SIGNAL
    //***************************************
    output logic 			   busy_o
    
    );
   
   localparam COMMAND_FIFO_WIDTH = TWD_QUEUE_ADD_WIDTH + TWD_QUEUE_ADD_WIDTH + MCHAN_LEN_WIDTH + TRANS_SID_WIDTH + 7; // INC, OPC, TWD_EXT, ELE, ILE, BLE, TWD_TCDM

   logic [TWD_COUNT_WIDTH-1:0] 			      s_twd_ext_queue_count;
   logic [TWD_STRIDE_WIDTH-1:0] 		      s_twd_ext_queue_stride;
   logic [TWD_COUNT_WIDTH-1:0] 			      s_twd_tcdm_queue_count;
   logic [TWD_STRIDE_WIDTH-1:0] 		      s_twd_tcdm_queue_stride;
   
   logic 					      s_cmd_req,s_cmd_req_fifo;
   logic 					      s_cmd_gnt,s_cmd_gnt_fifo;
   logic [MCHAN_LEN_WIDTH-1:0] 			      s_cmd_len;
   logic [MCHAN_OPC_WIDTH-1:0] 			      s_cmd_opc;
   logic 					      s_cmd_inc;
   logic 					      s_cmd_twd_ext;
   logic 					      s_cmd_ele;
   logic 					      s_cmd_ile;
   logic 					      s_cmd_ble;
   logic 					      s_cmd_twd_tcdm;
   logic [TWD_QUEUE_ADD_WIDTH-1:0] 		      s_cmd_twd_ext_add;
   logic [TWD_QUEUE_ADD_WIDTH-1:0] 		      s_cmd_twd_tcdm_add;
   logic [TRANS_SID_WIDTH-1:0] 			      s_cmd_sid;
   
   logic [TCDM_ADD_WIDTH-1:0] 			      s_tcdm_add;
   logic 					      s_tcdm_req,s_tcdm_req_fifo;
   logic 					      s_tcdm_gnt,s_tcdm_gnt_fifo;
   
   logic [EXT_ADD_WIDTH-1:0] 			      s_ext_add;
   logic 					      s_ext_req,s_ext_req_fifo;
   logic 					      s_ext_gnt,s_ext_gnt_fifo;
   
   logic 					      s_twd_ext_trans, s_twd_tcdm_trans,
						      s_twd_ext_last_trans, s_twd_tcdm_last_trans, 
						      s_twd_last_trans;
   
   logic                                              s_decoder_busy;

   logic 					      s_clk_enable;
   logic 					      s_clk_gated;
   
   genvar 					      i;
   
   //**********************************************************
   //*************** ADDRESS DECODER **************************
   //**********************************************************
   
   ctrl_fsm
     #(
       .TCDM_ADD_WIDTH(TCDM_ADD_WIDTH),
       .EXT_ADD_WIDTH(EXT_ADD_WIDTH),
       .NB_TRANSFERS(NB_TRANSFERS),
       .TWD_COUNT_WIDTH(TWD_COUNT_WIDTH),
       .TWD_STRIDE_WIDTH(TWD_STRIDE_WIDTH),
       .TWD_QUEUE_DEPTH(TWD_QUEUE_DEPTH),
       .PE_ID_WIDTH(PE_ID_WIDTH)
       )
   ctrl_fsm_i
     (
      
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .ctrl_targ_req_i(ctrl_targ_req_i),
      .ctrl_targ_type_i(ctrl_targ_type_i),
      .ctrl_targ_be_i(ctrl_targ_be_i),
      .ctrl_targ_add_i(ctrl_targ_add_i),
      .ctrl_targ_data_i(ctrl_targ_data_i),
      .ctrl_targ_id_i(ctrl_targ_id_i),
      .ctrl_targ_gnt_o(ctrl_targ_gnt_o),
      
      .ctrl_targ_r_valid_o(ctrl_targ_r_valid_o),
      .ctrl_targ_r_data_o(ctrl_targ_r_data_o),
      .ctrl_targ_r_opc_o(ctrl_targ_r_opc_o),
      .ctrl_targ_r_id_o(ctrl_targ_r_id_o),
      
      .cmd_gnt_i(s_cmd_gnt),
      .cmd_req_o(s_cmd_req),
      .cmd_len_o(s_cmd_len),
      .cmd_opc_o(s_cmd_opc),
      .cmd_inc_o(s_cmd_inc),
      .cmd_twd_ext_o(s_cmd_twd_ext),
      .cmd_ele_o(s_cmd_ele),
      .cmd_ile_o(s_cmd_ile),
      .cmd_ble_o(s_cmd_ble),
      .cmd_twd_tcdm_o(s_cmd_twd_tcdm),
      .cmd_twd_ext_add_o(s_cmd_twd_ext_add),
      .cmd_twd_tcdm_add_o(s_cmd_twd_tcdm_add),
      .cmd_sid_o(s_cmd_sid),
      
      .tcdm_gnt_i(s_tcdm_gnt),
      .tcdm_req_o(s_tcdm_req),
      .tcdm_add_o(s_tcdm_add),
      
      .ext_gnt_i(s_ext_gnt),
      .ext_req_o(s_ext_req),
      .ext_add_o(s_ext_add),
      
      .arb_gnt_i(arb_gnt_i),
      .arb_req_i(arb_req_i),
      .arb_sid_i(arb_sid_i),
      
      .twd_ext_trans_o(s_twd_ext_trans),
      
      .twd_ext_alloc_req_o(twd_ext_alloc_req_o),
      .twd_ext_alloc_gnt_i(twd_ext_alloc_gnt_i),
      .twd_ext_alloc_add_i(twd_ext_alloc_add_i),
      
      .twd_ext_queue_req_o(twd_ext_queue_req_o),
      .twd_ext_queue_add_o(twd_ext_queue_add_o),
      .twd_ext_queue_count_o(s_twd_ext_queue_count),
      .twd_ext_queue_stride_o(s_twd_ext_queue_stride),
      .twd_ext_queue_sid_o(twd_ext_queue_sid_o),
      
      .twd_tcdm_trans_o(s_twd_tcdm_trans),
      
      .twd_tcdm_alloc_req_o(twd_tcdm_alloc_req_o),
      .twd_tcdm_alloc_gnt_i(twd_tcdm_alloc_gnt_i),
      .twd_tcdm_alloc_add_i(twd_tcdm_alloc_add_i),
      
      .twd_tcdm_queue_req_o(twd_tcdm_queue_req_o),
      .twd_tcdm_queue_add_o(twd_tcdm_queue_add_o),
      .twd_tcdm_queue_count_o(s_twd_tcdm_queue_count),
      .twd_tcdm_queue_stride_o(s_twd_tcdm_queue_stride),
      .twd_tcdm_queue_sid_o(twd_tcdm_queue_sid_o),
      
      .trans_alloc_req_o(trans_alloc_req_o),
      .trans_alloc_gnt_i(trans_alloc_gnt_i),
      .trans_alloc_ret_i(trans_alloc_ret_i),
      .trans_alloc_clr_o(trans_alloc_clr_o),
      .trans_alloc_status_i(trans_alloc_status_i),
      
      .trans_status_i(trans_status_i),
      
      .busy_o(s_decoder_busy)
      
      );
   
   //**********************************************************
   //*************** COMMAND FIFO *****************************
   //**********************************************************
   
   generic_fifo
     #(
       .DATA_WIDTH(COMMAND_FIFO_WIDTH),
       .DATA_DEPTH(CTRL_TRANS_QUEUE_DEPTH)
       )
   command_fifo_i
     (
      
      .clk         (s_clk_gated),
      .rst_n       (rst_ni),

      .data_i      ({s_cmd_sid,s_cmd_twd_tcdm,s_cmd_ble,s_cmd_ile,s_cmd_ele,s_cmd_twd_ext,s_cmd_twd_tcdm_add,s_cmd_twd_ext_add,s_cmd_inc,s_cmd_opc,s_cmd_len}),
      .valid_i     (s_cmd_req),
      .grant_o     (s_cmd_gnt),
      
      .data_o      ({cmd_sid_o,cmd_twd_tcdm_o,cmd_ble_o,cmd_ile_o,cmd_ele_o,cmd_twd_ext_o,cmd_twd_tcdm_add_o,cmd_twd_ext_add_o,cmd_inc_o,cmd_opc_o,cmd_len_o}),
      .grant_i     (s_cmd_gnt_fifo),
      .valid_o     (s_cmd_req_fifo),

      .test_mode_i (test_mode_i)
      
      );
   
   //**********************************************************
   //*************** TCDM ADDR FIFO ***************************
   //**********************************************************
   
   generic_fifo
     #(
       .DATA_WIDTH(TCDM_ADD_WIDTH),
       .DATA_DEPTH(CTRL_TRANS_QUEUE_DEPTH)
       )
   tcdm_addr_fifo_i
     (
      .clk         (s_clk_gated),
      .rst_n       (rst_ni),
      
      .data_i      (s_tcdm_add),
      .valid_i     (s_tcdm_req),
      .grant_o     (s_tcdm_gnt),
      
      .data_o      (tcdm_add_o),
      .grant_i     (s_tcdm_gnt_fifo),
      .valid_o     (s_tcdm_req_fifo),

      .test_mode_i (test_mode_i)

      );
   
   //**********************************************************
   //*************** EXT ADDR FIFO ****************************
   //**********************************************************
   
   generic_fifo
     #(
       .DATA_WIDTH(EXT_ADD_WIDTH),
       .DATA_DEPTH(CTRL_TRANS_QUEUE_DEPTH)
       )
   ext_addr_fifo_i
     (
      
      .clk         (s_clk_gated),
      .rst_n       (rst_ni),
      
      .data_i      (s_ext_add),
      .valid_i     (s_ext_req),
      .grant_o     (s_ext_gnt),
      
      .data_o      (ext_add_o),
      .grant_i     (s_ext_gnt_fifo),
      .valid_o     (s_ext_req_fifo),

      .test_mode_i (test_mode_i)
      
      );
   
   cluster_clock_gating mchan_ctrl_ckgate
     (
      .clk_i      ( clk_i        ),
      .en_i       ( s_clk_enable ),
      .test_en_i  ( test_mode_i  ),
      .clk_o      ( s_clk_gated  )
      );
   
   //**********************************************************
   //******* BINDING OF QUEUE SIGNALS TWD ARBITER *************
   //**********************************************************
   
   assign busy_o                = s_decoder_busy;
   assign s_clk_enable          = (| trans_alloc_status_i) | s_decoder_busy;
   
   // TODO MANAGE 2D TRANS
   assign s_twd_ext_last_trans  = ( s_twd_ext_trans  == 1'b1 ) && ( s_twd_tcdm_trans == 1'b0 );
   assign s_twd_tcdm_last_trans = ( s_twd_tcdm_trans == 1'b1 );
   
   assign s_twd_last_trans      = ( s_twd_ext_last_trans == 1 && twd_ext_queue_req_o == 0 ) || ( s_twd_tcdm_last_trans == 1 && twd_tcdm_queue_req_o == 0 );
   
   assign cmd_req_o        = s_ext_req_fifo && s_tcdm_req_fifo && s_cmd_req_fifo && ( ! s_twd_last_trans ) ;
   assign s_ext_gnt_fifo   = cmd_gnt_i;
   assign s_tcdm_gnt_fifo  = cmd_gnt_i;
   assign s_cmd_gnt_fifo   = cmd_gnt_i;
   
   assign twd_ext_queue_dat_o  = {s_twd_ext_queue_stride,s_twd_ext_queue_count};
   assign twd_tcdm_queue_dat_o = {s_twd_tcdm_queue_stride,s_twd_tcdm_queue_count};
   
endmodule
