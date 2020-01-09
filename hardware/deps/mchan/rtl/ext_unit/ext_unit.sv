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

module ext_unit
  #(
    parameter AXI_ADDR_WIDTH  = 32,
    parameter AXI_DATA_WIDTH  = 64,
    parameter AXI_USER_WIDTH  = 6,
    parameter AXI_ID_WIDTH    = 4,
    parameter AXI_STRB_WIDTH  = AXI_DATA_WIDTH/8,
    parameter TRANS_SID_WIDTH = 1,
    parameter EXT_ADD_WIDTH   = 29,
    parameter EXT_OPC_WIDTH   = 12,
    parameter EXT_TID_WIDTH   = 4,
    parameter TCDM_ADD_WIDTH  = 12,
    parameter TCDM_OPC_WIDTH  = 12,
    parameter MCHAN_LEN_WIDTH = 15
    )
   (
    input  logic                        clk_i,
    input  logic                        rst_ni,

    input  logic                        test_mode_i,
    
    // AXI4 MASTER
    //***************************************
    // WRITE ADDRESS CHANNEL
    output logic                        axi_master_aw_valid_o,
    output logic [AXI_ADDR_WIDTH-1:0]   axi_master_aw_addr_o,
    output logic [2:0]                  axi_master_aw_prot_o,
    output logic [3:0]                  axi_master_aw_region_o,
    output logic [7:0]                  axi_master_aw_len_o,
    output logic [2:0]                  axi_master_aw_size_o,
    output logic [1:0]                  axi_master_aw_burst_o,
    output logic                        axi_master_aw_lock_o,
    output logic [3:0]                  axi_master_aw_cache_o,
    output logic [3:0]                  axi_master_aw_qos_o,
    output logic [AXI_ID_WIDTH-1:0]     axi_master_aw_id_o,
    output logic [AXI_USER_WIDTH-1:0]   axi_master_aw_user_o,
    input  logic                        axi_master_aw_ready_i,
    
    // READ ADDRESS CHANNEL
    output logic                        axi_master_ar_valid_o,
    output logic [AXI_ADDR_WIDTH-1:0]   axi_master_ar_addr_o,
    output logic [2:0]                  axi_master_ar_prot_o,
    output logic [3:0]                  axi_master_ar_region_o,
    output logic [7:0]                  axi_master_ar_len_o,
    output logic [2:0]                  axi_master_ar_size_o,
    output logic [1:0]                  axi_master_ar_burst_o,
    output logic                        axi_master_ar_lock_o,
    output logic [3:0]                  axi_master_ar_cache_o,
    output logic [3:0]                  axi_master_ar_qos_o,
    output logic [AXI_ID_WIDTH-1:0]     axi_master_ar_id_o,
    output logic [AXI_USER_WIDTH-1:0]   axi_master_ar_user_o,
    input  logic                        axi_master_ar_ready_i,
    
    // WRITE DATA CHANNEL
    output logic                        axi_master_w_valid_o,
    output logic [AXI_DATA_WIDTH-1:0]   axi_master_w_data_o,
    output logic [AXI_STRB_WIDTH-1:0]   axi_master_w_strb_o,
    output logic [AXI_USER_WIDTH-1:0]   axi_master_w_user_o,
    output logic                        axi_master_w_last_o,
    input  logic                        axi_master_w_ready_i,
    
    // READ DATA CHANNEL
    input  logic                        axi_master_r_valid_i,
    input  logic [AXI_DATA_WIDTH-1:0]   axi_master_r_data_i,
    input  logic [1:0]                  axi_master_r_resp_i,
    input  logic                        axi_master_r_last_i,
    input  logic [AXI_ID_WIDTH-1:0]     axi_master_r_id_i,
    input  logic [AXI_USER_WIDTH-1:0]   axi_master_r_user_i,
    output logic                        axi_master_r_ready_o,
    
    // WRITE RESPONSE CHANNEL
    input  logic                        axi_master_b_valid_i,
    input  logic [1:0]                  axi_master_b_resp_i,
    input  logic [AXI_ID_WIDTH-1:0]     axi_master_b_id_i,
    input  logic [AXI_USER_WIDTH-1:0]   axi_master_b_user_i,
    output logic                        axi_master_b_ready_o,
    
    // INPUT CMD INTERFACE
    input  logic [TRANS_SID_WIDTH-1:0]  ext_rx_sid_i,
    input  logic [EXT_ADD_WIDTH-1:0]    ext_rx_add_i,
    input  logic [TCDM_ADD_WIDTH-1:0]   ext_rx_r_add_i,
    input  logic [TCDM_OPC_WIDTH-1:0]   ext_rx_opc_i,
    input  logic [MCHAN_LEN_WIDTH-1:0]  ext_rx_len_i,
    input  logic                        ext_rx_bst_i,
    input  logic                        ext_rx_req_i,
    output logic                        ext_rx_gnt_o,
    
    input  logic [TRANS_SID_WIDTH-1:0]  ext_tx_sid_i,
    input  logic [EXT_ADD_WIDTH-1:0]    ext_tx_add_i,
    input  logic [TCDM_OPC_WIDTH-1:0]   ext_tx_opc_i,
    input  logic [MCHAN_LEN_WIDTH-1:0]  ext_tx_len_i,
    input  logic                        ext_tx_bst_i,
    input  logic                        ext_tx_req_i,
    output logic                        ext_tx_gnt_o,
    
    // OUT CMD INTERFACE TO TCDM UNIT
    //***************************************
    output logic [TRANS_SID_WIDTH-1:0]  tcdm_rx_sid_o,
    output logic [TCDM_ADD_WIDTH-1:0]   tcdm_rx_add_o,
    output logic [TCDM_OPC_WIDTH-1:0]   tcdm_rx_opc_o,
    output logic [MCHAN_LEN_WIDTH-1:0]  tcdm_rx_len_o,
    output logic                        tcdm_rx_req_o,
    input  logic                        tcdm_rx_gnt_i,
    
    // OUT CMD INTERFACE TO TRANS UNIT
    //***************************************
    output logic [2:0]                  trans_rx_ext_add_o,
    output logic [2:0]                  trans_rx_tcdm_add_o,
    output logic [MCHAN_LEN_WIDTH-1:0]  trans_rx_len_o,
    output logic                        trans_rx_req_o,
    input  logic                        trans_rx_gnt_i,
    
    // OUT SYNCHRONIZATION INTERFACES
    //***************************************
    output logic                        tx_synch_req_o,
    output logic [TRANS_SID_WIDTH-1:0]  tx_synch_sid_o,
    
    output logic                        rx_synch_req_o,
    output logic [TRANS_SID_WIDTH-1:0]  rx_synch_sid_o,
    
    // WRITE DATA INTERFACE
    //***************************************
    input  logic [63:0]                 tx_data_dat_i,
    input  logic [7:0]                  tx_data_strb_i,
    output logic                        tx_data_req_o,
    input  logic                        tx_data_gnt_i,
    
    // READ DATA INTERFACE
    //***************************************
    output logic [63:0]                 rx_data_dat_o,
    output logic                        rx_data_req_o,
    input  logic                        rx_data_gnt_i
    
    );
   
   localparam EXT_TX_CMD_QUEUE_WIDTH = EXT_OPC_WIDTH + MCHAN_LEN_WIDTH + EXT_ADD_WIDTH + TRANS_SID_WIDTH +1; //BST
   localparam EXT_RX_CMD_QUEUE_WIDTH = EXT_OPC_WIDTH + MCHAN_LEN_WIDTH + EXT_ADD_WIDTH + TCDM_ADD_WIDTH + TRANS_SID_WIDTH + 1; // BST
   
   logic 			       s_rx_req,s_tx_req;
   logic 			       s_rx_gnt,s_tx_gnt;
   logic                               s_rx_bst,s_tx_bst;
   logic [TRANS_SID_WIDTH-1:0] 	       s_rx_sid,s_tx_sid;
   logic [EXT_ADD_WIDTH-1:0] 	       s_rx_add,s_tx_add;
   logic [EXT_TID_WIDTH-1:0] 	       s_rx_tid,s_tx_tid;
   logic [TCDM_ADD_WIDTH-1:0] 	       s_rx_r_add;
   logic [EXT_OPC_WIDTH-1:0] 	       s_rx_opc,s_tx_opc;
   logic [MCHAN_LEN_WIDTH-1:0] 	       s_rx_len,s_tx_len;
   
   logic 			       s_rx_release_tid,s_tx_release_tid;
   logic 			       s_rx_valid_tid,s_tx_valid_tid;
   logic [EXT_TID_WIDTH-1:0] 	       s_rx_res_tid,s_tx_res_tid;
   
   // SIGNAL DECLARATION
   logic 			       s_aw_valid;
   logic [AXI_ADDR_WIDTH-1:0] 	       s_aw_addr;
   logic [2:0] 			       s_aw_prot;
   logic [3:0] 			       s_aw_region;
   logic [7:0] 			       s_aw_len;
   logic [2:0] 			       s_aw_size;
   logic [1:0] 			       s_aw_burst;
   logic 			       s_aw_lock;
   logic [3:0] 			       s_aw_cache;
   logic [3:0] 			       s_aw_qos;
   logic [AXI_ID_WIDTH-1:0] 	       s_aw_id;
   logic [AXI_USER_WIDTH-1:0] 	       s_aw_user;
   logic 			       s_aw_ready;
   
   logic 			       s_ar_valid;
   logic [AXI_ADDR_WIDTH-1:0] 	       s_ar_addr;
   logic [2:0] 			       s_ar_prot;
   logic [3:0] 			       s_ar_region;
   logic [7:0] 			       s_ar_len;
   logic [2:0] 			       s_ar_size;
   logic [1:0] 			       s_ar_burst;
   logic 			       s_ar_lock;
   logic [3:0] 			       s_ar_cache;
   logic [3:0] 			       s_ar_qos;
   logic [AXI_ID_WIDTH-1:0] 	       s_ar_id;
   logic [AXI_USER_WIDTH-1:0] 	       s_ar_user;
   logic 			       s_ar_ready;
   
   logic 			       s_w_valid;
   logic [AXI_DATA_WIDTH-1:0] 	       s_w_data;
   logic [AXI_STRB_WIDTH-1:0] 	       s_w_strb;
   logic [AXI_USER_WIDTH-1:0] 	       s_w_user;
   logic 			       s_w_last;
   logic 			       s_w_ready;
   
   logic 			       s_r_valid;
   logic [AXI_DATA_WIDTH-1:0] 	       s_r_data;
   logic [1:0] 			       s_r_resp;
   logic 			       s_r_last;
   logic [AXI_ID_WIDTH-1:0] 	       s_r_id;
   logic [AXI_USER_WIDTH-1:0] 	       s_r_user;
   logic 			       s_r_ready;
   
   logic 			       s_b_valid;
   logic [1:0] 			       s_b_resp;
   logic [AXI_ID_WIDTH-1:0] 	       s_b_id;
   logic [AXI_USER_WIDTH-1:0] 	       s_b_user;
   logic 			       s_b_ready;
   
   //**********************************************************
   //*************** TX COMMAND QUEUE *************************
   //**********************************************************
   
   generic_fifo
     #(
       .DATA_WIDTH(EXT_TX_CMD_QUEUE_WIDTH),
       .DATA_DEPTH(2)
       )
   tx_cmd_queue_i
     (
      
      .clk         (clk_i),
      .rst_n       (rst_ni),
      
      .data_i      ({ext_tx_bst_i,ext_tx_opc_i,ext_tx_len_i,ext_tx_add_i,ext_tx_sid_i}),
      .valid_i     (ext_tx_req_i),
      .grant_o     (ext_tx_gnt_o),
      
      .data_o      ({s_tx_bst,s_tx_opc,s_tx_len,s_tx_add,s_tx_sid}),
      .grant_i     (s_tx_gnt),
      .valid_o     (s_tx_req),

      .test_mode_i (test_mode_i)
      
      );
   
   //**********************************************************
   //*************** RX COMMAND QUEUE *************************
   //**********************************************************
   
   generic_fifo
     #(
       .DATA_WIDTH(EXT_RX_CMD_QUEUE_WIDTH),
       .DATA_DEPTH(2)
       )
   rx_cmd_queue_i
     (
      
      .clk         (clk_i),
      .rst_n       (rst_ni),
      
      .data_i      ({ext_rx_bst_i,ext_rx_opc_i,ext_rx_len_i,ext_rx_add_i,ext_rx_r_add_i,ext_rx_sid_i}),
      .valid_i     (ext_rx_req_i),
      .grant_o     (ext_rx_gnt_o),
      
      .data_o      ({s_rx_bst,s_rx_opc,s_rx_len,s_rx_add,s_rx_r_add,s_rx_sid}),
      .grant_i     (s_rx_gnt),
      .valid_o     (s_rx_req),

      .test_mode_i (test_mode_i)
      
      );
   
   //**********************************************************
   //*************** EXT TX INTERFACE *************************
   //**********************************************************
   
   ext_tx_if
     #(
       .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
       .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
       .AXI_USER_WIDTH(AXI_USER_WIDTH),
       .AXI_ID_WIDTH(AXI_ID_WIDTH),
       .AXI_STRB_WIDTH(AXI_STRB_WIDTH),
       .EXT_ADD_WIDTH(EXT_ADD_WIDTH),
       .EXT_TID_WIDTH(EXT_TID_WIDTH),
       .EXT_OPC_WIDTH(EXT_OPC_WIDTH),
       .MCHAN_LEN_WIDTH(MCHAN_LEN_WIDTH)
       )
   ext_tx_if_i
     (
      
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .cmd_add_i(s_tx_add),
      .cmd_opc_i(s_tx_opc),
      .cmd_len_i(s_tx_len),
      .cmd_tid_i(s_tx_tid),
      .cmd_bst_i(s_tx_bst),
      .cmd_req_i(s_tx_req),
      .cmd_gnt_o(s_tx_gnt),
      
      .valid_tid_i(s_tx_valid_tid),
      
      .release_tid_o(s_tx_release_tid),
      .res_tid_o(s_tx_res_tid),
      
      .synch_req_o(tx_synch_req_o),
      
      .tx_data_dat_i(tx_data_dat_i),
      .tx_data_strb_i(tx_data_strb_i),
      .tx_data_req_o(tx_data_req_o),
      .tx_data_gnt_i(tx_data_gnt_i),
      
      .axi_master_aw_valid_o(s_aw_valid),
      .axi_master_aw_addr_o(s_aw_addr),
      .axi_master_aw_prot_o(s_aw_prot),
      .axi_master_aw_region_o(s_aw_region),
      .axi_master_aw_len_o(s_aw_len),
      .axi_master_aw_size_o(s_aw_size),
      .axi_master_aw_burst_o(s_aw_burst),
      .axi_master_aw_lock_o(s_aw_lock),
      .axi_master_aw_cache_o(s_aw_cache),
      .axi_master_aw_qos_o(s_aw_qos),
      .axi_master_aw_id_o(s_aw_id),
      .axi_master_aw_user_o(s_aw_user),
      .axi_master_aw_ready_i(s_aw_ready),
      
      .axi_master_w_valid_o(s_w_valid),
      .axi_master_w_data_o(s_w_data),
      .axi_master_w_strb_o(s_w_strb),
      .axi_master_w_user_o(s_w_user),
      .axi_master_w_last_o(s_w_last),
      .axi_master_w_ready_i(s_w_ready),
      
      .axi_master_b_valid_i(s_b_valid),
      .axi_master_b_resp_i(s_b_resp),
      .axi_master_b_id_i(s_b_id),
      .axi_master_b_user_i(s_b_user),
      .axi_master_b_ready_o(s_b_ready)
      
      );
   
   //**********************************************************
   //*************** EXT RX INTERFACE *************************
   //**********************************************************
   
   ext_rx_if
     #(
       .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
       .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
       .AXI_USER_WIDTH(AXI_USER_WIDTH),
       .AXI_ID_WIDTH(AXI_ID_WIDTH),
       .AXI_STRB_WIDTH(AXI_STRB_WIDTH),
       .EXT_ADD_WIDTH(EXT_ADD_WIDTH),
       .EXT_OPC_WIDTH(EXT_OPC_WIDTH),
       .EXT_TID_WIDTH(EXT_TID_WIDTH),
       .MCHAN_LEN_WIDTH(MCHAN_LEN_WIDTH)
       )
   ext_rx_if_i
     (
      
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .cmd_add_i(s_rx_add),
      .cmd_opc_i(s_rx_opc),
      .cmd_len_i(s_rx_len),
      .cmd_tid_i(s_rx_tid),
      .cmd_bst_i(s_rx_bst),
      .cmd_req_i(s_rx_req),
      .cmd_gnt_o(s_rx_gnt),
      
      .tcdm_req_o(tcdm_rx_req_o),
      .tcdm_gnt_i(tcdm_rx_gnt_i),
      
      .trans_rx_req_o(trans_rx_req_o),
      .trans_rx_gnt_i(trans_rx_gnt_i),
      
      .valid_tid_i(s_rx_valid_tid),
      
      .release_tid_o(s_rx_release_tid),
      .res_tid_o(s_rx_res_tid),
      
      .synch_req_o(rx_synch_req_o),
      
      .rx_data_dat_o(rx_data_dat_o),
      .rx_data_req_o(rx_data_req_o),
      .rx_data_gnt_i(rx_data_gnt_i),
      
      .axi_master_ar_valid_o(s_ar_valid),
      .axi_master_ar_addr_o(s_ar_addr),
      .axi_master_ar_prot_o(s_ar_prot),
      .axi_master_ar_region_o(s_ar_region),
      .axi_master_ar_len_o(s_ar_len),
      .axi_master_ar_size_o(s_ar_size),
      .axi_master_ar_burst_o(s_ar_burst),
      .axi_master_ar_lock_o(s_ar_lock),
      .axi_master_ar_cache_o(s_ar_cache),
      .axi_master_ar_qos_o(s_ar_qos),
      .axi_master_ar_id_o(s_ar_id),
      .axi_master_ar_user_o(s_ar_user),
      .axi_master_ar_ready_i(s_ar_ready),
      
      .axi_master_r_valid_i(s_r_valid),
      .axi_master_r_data_i(s_r_data),
      .axi_master_r_resp_i(s_r_resp),
      .axi_master_r_last_i(s_r_last),
      .axi_master_r_id_i(s_r_id),
      .axi_master_r_user_i(s_r_user),
      .axi_master_r_ready_o(s_r_ready)
      
      );
   
   //**********************************************************
   //*************** TID COMPUTE MODULE ***********************
   //**********************************************************
   
   // TX TID GEN
   ext_tid_gen
     #(
       .EXT_TID_WIDTH(EXT_TID_WIDTH)
       )
   tx_tid_gen_i
     (
      
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .valid_tid_o(s_tx_valid_tid),
      
      .tid_o(s_tx_tid),
      .incr_i(s_tx_gnt && s_tx_req),
      
      .tid_i(s_tx_res_tid),
      .release_tid_i(s_tx_release_tid)
      
      );
   
   // RX TID GEN
   ext_tid_gen
     #(
       .EXT_TID_WIDTH(EXT_TID_WIDTH)
       )
   rx_tid_gen_i
     (
      
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .valid_tid_o(s_rx_valid_tid),
      
      .tid_o(s_rx_tid),
      .incr_i(s_rx_gnt && s_rx_req),
      
      .tid_i(s_rx_res_tid),
      .release_tid_i(s_rx_release_tid)
      
      );
   
   //**********************************************************
   //*************** OPC BUFFER *******************************
   //**********************************************************
   
   ext_opc_buf
     #(
       .TRANS_SID_WIDTH(TRANS_SID_WIDTH),
       .TCDM_ADD_WIDTH(TCDM_ADD_WIDTH),
       .TCDM_OPC_WIDTH(TCDM_OPC_WIDTH),
       .EXT_TID_WIDTH(EXT_TID_WIDTH),
       .MCHAN_LEN_WIDTH(MCHAN_LEN_WIDTH)
       )
   rx_opc_buf_i
     (
      
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .tid_valid_i(s_rx_gnt & s_rx_req & s_rx_valid_tid),
      .tid_i(s_rx_tid),
      .opc_i(s_rx_opc),
      .len_i(s_rx_len),
      .add_i(s_rx_add[2:0]),
      .r_add_i(s_rx_r_add),
      .sid_i(s_rx_sid),
      
      .r_tid_i(s_r_id[EXT_TID_WIDTH-1:0]),
      
      .tcdm_opc_o(tcdm_rx_opc_o),
      .tcdm_len_o(tcdm_rx_len_o),
      .tcdm_add_o(tcdm_rx_add_o),
      .tcdm_sid_o(tcdm_rx_sid_o),
      
      .trans_rx_ext_add_o(trans_rx_ext_add_o),
      .trans_rx_tcdm_add_o(trans_rx_tcdm_add_o),
      .trans_rx_len_o(trans_rx_len_o),
      
      .synch_sid_o(rx_synch_sid_o)
      
      );
   
   ext_opc_buf
     #(
       .TRANS_SID_WIDTH(TRANS_SID_WIDTH),
       .TCDM_ADD_WIDTH(TCDM_ADD_WIDTH),
       .TCDM_OPC_WIDTH(TCDM_OPC_WIDTH),
       .EXT_TID_WIDTH(EXT_TID_WIDTH),
       .MCHAN_LEN_WIDTH(MCHAN_LEN_WIDTH)
       )
   tx_opc_buf_i
     (
      
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .tid_valid_i(s_tx_gnt & s_tx_req & s_tx_valid_tid),
      .tid_i(s_tx_tid),
      .opc_i('0),
      .len_i('0),
      .add_i('0),
      .r_add_i('0),
      .sid_i(s_tx_sid),
      
      .r_tid_i(s_b_id[EXT_TID_WIDTH-1:0]),
      
      .tcdm_opc_o(),
      .tcdm_len_o(),
      .tcdm_add_o(),
      .tcdm_sid_o(),
      
      .trans_rx_ext_add_o(),
      .trans_rx_tcdm_add_o(),
      .trans_rx_len_o(),
      
      .synch_sid_o(tx_synch_sid_o)
      
      );
   
   //**********************************************************
   //*************** AXI REGISTER SLICES **********************
   //**********************************************************
   
   ext_aw_buffer
     #(
       .ID_WIDTH(AXI_ID_WIDTH),
       .ADDR_WIDTH(AXI_ADDR_WIDTH),
       .USER_WIDTH(AXI_USER_WIDTH)
       )
   aw_buffer_i
     (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .slave_valid_i(s_aw_valid),
      .slave_addr_i(s_aw_addr),
      .slave_prot_i(s_aw_prot),
      .slave_region_i(s_aw_region),
      .slave_len_i(s_aw_len),
      .slave_size_i(s_aw_size),
      .slave_burst_i(s_aw_burst),
      .slave_lock_i(s_aw_lock),
      .slave_cache_i(s_aw_cache),
      .slave_qos_i(s_aw_qos),
      .slave_id_i(s_aw_id),
      .slave_user_i(s_aw_user),
      .slave_ready_o(s_aw_ready),
      
      .master_valid_o(axi_master_aw_valid_o),
      .master_addr_o(axi_master_aw_addr_o),
      .master_prot_o(axi_master_aw_prot_o),
      .master_region_o(axi_master_aw_region_o),
      .master_len_o(axi_master_aw_len_o),
      .master_size_o(axi_master_aw_size_o),
      .master_burst_o(axi_master_aw_burst_o),
      .master_lock_o(axi_master_aw_lock_o),
      .master_cache_o(axi_master_aw_cache_o),
      .master_qos_o(axi_master_aw_qos_o),
      .master_id_o(axi_master_aw_id_o),
      .master_user_o(axi_master_aw_user_o),
      .master_ready_i(axi_master_aw_ready_i)
      );
   
   // AXI READ ADDRESS CHANNEL BUFFER
   ext_ar_buffer
     #(
       .ID_WIDTH(AXI_ID_WIDTH),
       .ADDR_WIDTH(AXI_ADDR_WIDTH),
       .USER_WIDTH(AXI_USER_WIDTH)
       )
   ar_buffer_i
     (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .slave_valid_i(s_ar_valid),
      .slave_addr_i(s_ar_addr),
      .slave_prot_i(s_ar_prot),
      .slave_region_i(s_ar_region),
      .slave_len_i(s_ar_len),
      .slave_size_i(s_ar_size),
      .slave_burst_i(s_ar_burst),
      .slave_lock_i(s_ar_lock),
      .slave_cache_i(s_ar_cache),
      .slave_qos_i(s_ar_qos),
      .slave_id_i(s_ar_id),
      .slave_user_i(s_ar_user),
      .slave_ready_o(s_ar_ready),
      
      .master_valid_o(axi_master_ar_valid_o),
      .master_addr_o(axi_master_ar_addr_o),
      .master_prot_o(axi_master_ar_prot_o),
      .master_region_o(axi_master_ar_region_o),
      .master_len_o(axi_master_ar_len_o),
      .master_size_o(axi_master_ar_size_o),
      .master_burst_o(axi_master_ar_burst_o),
      .master_lock_o(axi_master_ar_lock_o),
      .master_cache_o(axi_master_ar_cache_o),
      .master_qos_o(axi_master_ar_qos_o),
      .master_id_o(axi_master_ar_id_o),
      .master_user_o(axi_master_ar_user_o),
      .master_ready_i(axi_master_ar_ready_i)
      );
   
   // WRITE DATA CHANNEL BUFFER
   ext_w_buffer
     #(
       .DATA_WIDTH(AXI_DATA_WIDTH),
       .USER_WIDTH(AXI_USER_WIDTH)
       )
   w_buffer_i
     (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .slave_valid_i(s_w_valid),
      .slave_data_i(s_w_data),
      .slave_strb_i(s_w_strb),
      .slave_user_i(s_w_user),
      .slave_last_i(s_w_last),
      .slave_ready_o(s_w_ready),
      
      .master_valid_o(axi_master_w_valid_o),
      .master_data_o(axi_master_w_data_o),
      .master_strb_o(axi_master_w_strb_o),
      .master_user_o(axi_master_w_user_o),
      .master_last_o(axi_master_w_last_o),
      .master_ready_i(axi_master_w_ready_i)
      );
   
   // READ DATA CHANNEL BUFFER
   ext_r_buffer
     #(
       .ID_WIDTH(AXI_ID_WIDTH),
       .DATA_WIDTH(AXI_DATA_WIDTH),
       .USER_WIDTH(AXI_USER_WIDTH)
       )
   r_buffer_i
     (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .slave_valid_i(axi_master_r_valid_i),
      .slave_data_i(axi_master_r_data_i),
      .slave_resp_i(axi_master_r_resp_i),
      .slave_user_i(axi_master_r_user_i),
      .slave_id_i(axi_master_r_id_i),
      .slave_last_i(axi_master_r_last_i),
      .slave_ready_o(axi_master_r_ready_o),
      
      .master_valid_o(s_r_valid),
      .master_data_o(s_r_data),
      .master_resp_o(s_r_resp),
      .master_user_o(s_r_user),
      .master_id_o(s_r_id),
      .master_last_o(s_r_last),
      .master_ready_i(s_r_ready)
      );
   
   // WRITE RESPONSE CHANNEL BUFFER
   ext_b_buffer
     #(
       .ID_WIDTH(AXI_ID_WIDTH),
       .USER_WIDTH(AXI_USER_WIDTH)
       )
   b_buffer_i
     (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .slave_valid_i(axi_master_b_valid_i),
      .slave_resp_i(axi_master_b_resp_i),
      .slave_id_i(axi_master_b_id_i),
      .slave_user_i(axi_master_b_user_i),
      .slave_ready_o(axi_master_b_ready_o),
      
      .master_valid_o(s_b_valid),
      .master_resp_o(s_b_resp),
      .master_id_o(s_b_id),
      .master_user_o(s_b_user),
      .master_ready_i(s_b_ready)
   );
   
endmodule
