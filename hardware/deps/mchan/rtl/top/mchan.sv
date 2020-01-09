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

module mchan
#( 
    parameter NB_CTRLS                 = 4,  // NUMBER OF CTRLS
    parameter NB_TRANSFERS             = 8,  // NUMBER OF TRANSFERS
    
    parameter CTRL_TRANS_QUEUE_DEPTH   = 2,  // DEPTH OF PRIVATE PER-CTRL COMMAND QUEUE (CTRL_UNIT)
    parameter GLOBAL_TRANS_QUEUE_DEPTH = 2,  // DEPTH OF GLOBAL COMMAND QUEUE (CTRL_UNIT)
    parameter TWD_QUEUE_DEPTH          = 4,  // DEPTH OF GLOBAL 2D COMMAND QUEUE (CTRL_UNIT)
    
    parameter TCDM_ADD_WIDTH           = 16, // WIDTH OF TCDM ADDRESS
    parameter EXT_ADD_WIDTH            = 32, // WIDTH OF GLOBAL EXTERNAL ADDRESS
    
    parameter NB_OUTSND_TRANS          = 8,  // NUMBER OF OUTSTANDING TRANSACTIONS
    parameter MCHAN_BURST_LENGTH       = 64, // ANY POWER OF 2 VALUE FROM 8 TO 2048
    
    parameter AXI_ADDR_WIDTH           = 32,
    parameter AXI_DATA_WIDTH           = 64,
    parameter AXI_USER_WIDTH           = 6,
    parameter AXI_ID_WIDTH             = 4,
    parameter AXI_STRB_WIDTH           = AXI_DATA_WIDTH/8,

    parameter PE_ID_WIDTH              = 1,
    parameter TRANS_SID_WIDTH          = (NB_TRANSFERS == 1) ? 1 : $clog2(NB_TRANSFERS)
)
(
    
    input  logic                      clk_i,
    input  logic                      rst_ni,
    
    input logic                       test_mode_i,
    
    // CONTROL TARGET
    //***************************************
    input  logic [NB_CTRLS-1:0]       ctrl_targ_req_i,
    input  logic [NB_CTRLS-1:0]       ctrl_targ_type_i,
    input  logic [NB_CTRLS-1:0][3:0]  ctrl_targ_be_i,
    input  logic [NB_CTRLS-1:0][31:0] ctrl_targ_add_i,
    input  logic [NB_CTRLS-1:0][31:0] ctrl_targ_data_i,
    input  logic [NB_CTRLS-1:0][PE_ID_WIDTH-1:0] ctrl_targ_id_i,
    output logic [NB_CTRLS-1:0]       ctrl_targ_gnt_o,
    
    output logic [NB_CTRLS-1:0]       ctrl_targ_r_valid_o,
    output logic [NB_CTRLS-1:0][31:0] ctrl_targ_r_data_o,
    output logic [NB_CTRLS-1:0]       ctrl_targ_r_opc_o,
    output logic [NB_CTRLS-1:0][PE_ID_WIDTH-1:0] ctrl_targ_r_id_o,
    
    // TCDM INITIATOR
    //***************************************
    output logic [3:0]                      tcdm_init_req_o,
    output logic [3:0][31:0]                tcdm_init_add_o,
    output logic [3:0]                      tcdm_init_type_o,
    output logic [3:0][3:0]                 tcdm_init_be_o,
    output logic [3:0][31:0]                tcdm_init_data_o,
    output logic [3:0][TRANS_SID_WIDTH-1:0] tcdm_init_sid_o,
    input  logic [3:0]                      tcdm_init_gnt_i,
    
    input  logic [3:0]                      tcdm_init_r_valid_i,
    input  logic [3:0][31:0]                tcdm_init_r_data_i,
    
    // AXI4 MASTER
    //***************************************
    // WRITE ADDRESS CHANNEL
    output logic                      axi_master_aw_valid_o,
    output logic [AXI_ADDR_WIDTH-1:0] axi_master_aw_addr_o,
    output logic [2:0]                axi_master_aw_prot_o,
    output logic [3:0]                axi_master_aw_region_o,
    output logic [7:0]                axi_master_aw_len_o,
    output logic [2:0]                axi_master_aw_size_o,
    output logic [1:0]                axi_master_aw_burst_o,
    output logic                      axi_master_aw_lock_o,
    output logic [3:0]                axi_master_aw_cache_o,
    output logic [3:0]                axi_master_aw_qos_o,
    output logic [AXI_ID_WIDTH-1:0]   axi_master_aw_id_o,
    output logic [AXI_USER_WIDTH-1:0] axi_master_aw_user_o,
    input  logic                      axi_master_aw_ready_i,
    
    // READ ADDRESS CHANNEL
    output logic                      axi_master_ar_valid_o,
    output logic [AXI_ADDR_WIDTH-1:0] axi_master_ar_addr_o,
    output logic [2:0]                axi_master_ar_prot_o,
    output logic [3:0]                axi_master_ar_region_o,
    output logic [7:0]                axi_master_ar_len_o,
    output logic [2:0]                axi_master_ar_size_o,
    output logic [1:0]                axi_master_ar_burst_o,
    output logic                      axi_master_ar_lock_o,
    output logic [3:0]                axi_master_ar_cache_o,
    output logic [3:0]                axi_master_ar_qos_o,
    output logic [AXI_ID_WIDTH-1:0]   axi_master_ar_id_o,
    output logic [AXI_USER_WIDTH-1:0] axi_master_ar_user_o,
    input  logic                      axi_master_ar_ready_i,
    
    // WRITE DATA CHANNEL
    output logic                      axi_master_w_valid_o,
    output logic [AXI_DATA_WIDTH-1:0] axi_master_w_data_o,
    output logic [AXI_STRB_WIDTH-1:0] axi_master_w_strb_o,
    output logic [AXI_USER_WIDTH-1:0] axi_master_w_user_o,
    output logic                      axi_master_w_last_o,
    input  logic                      axi_master_w_ready_i,
    
    // READ DATA CHANNEL
    input  logic                      axi_master_r_valid_i,
    input  logic [AXI_DATA_WIDTH-1:0] axi_master_r_data_i,
    input  logic [1:0]                axi_master_r_resp_i,
    input  logic                      axi_master_r_last_i,
    input  logic [AXI_ID_WIDTH-1:0]   axi_master_r_id_i,
    input  logic [AXI_USER_WIDTH-1:0] axi_master_r_user_i,
    output logic                      axi_master_r_ready_o,
    
    // WRITE RESPONSE CHANNEL
    input  logic                      axi_master_b_valid_i,
    input  logic [1:0]                axi_master_b_resp_i,
    input  logic [AXI_ID_WIDTH-1:0]   axi_master_b_id_i,
    input  logic [AXI_USER_WIDTH-1:0] axi_master_b_user_i,
    output logic                      axi_master_b_ready_o,
    
    // TERMINATION EVENTS
    //***************************************
    output logic [NB_CTRLS-1:0]       term_evt_o,
    output logic [NB_CTRLS-1:0]       term_int_o,
    
    // BUSY SIGNAL
    //***************************************
    output logic                      busy_o
    
    );
   
   // LOCAL PARAMETERS
   
   localparam TCDM_OPC_WIDTH  = `TCDM_OPC_WIDTH;
   localparam EXT_OPC_WIDTH   = `EXT_OPC_WIDTH;
   localparam MCHAN_LEN_WIDTH = `MCHAN_LEN_WIDTH;
   localparam EXT_TID_WIDTH   = (NB_OUTSND_TRANS ==1) ? 1 : $clog2(NB_OUTSND_TRANS);
   
   // SIGNALS
   logic                              s_clk_gated;
   
   logic                              s_tcdm_tx_req, s_tcdm_rx_req, s_ext_tx_req, s_ext_rx_req;
   logic                              s_tcdm_tx_gnt, s_tcdm_rx_gnt, s_ext_tx_gnt, s_ext_rx_gnt;
   logic                              s_ext_tx_bst, s_ext_rx_bst;     
   logic [MCHAN_LEN_WIDTH-1:0]        s_tcdm_tx_len, s_tcdm_rx_len, s_ext_tx_len, s_ext_rx_len;
   logic [TCDM_OPC_WIDTH-1:0] 	      s_tcdm_tx_opc, s_tcdm_rx_opc;
   logic [TCDM_OPC_WIDTH-1:0]         s_ext_tx_opc, s_ext_rx_opc;
   logic [TCDM_ADD_WIDTH-1:0]         s_tcdm_tx_add, s_tcdm_rx_add;
   logic [EXT_ADD_WIDTH-1:0]          s_ext_tx_add, s_ext_rx_add;
   logic [TCDM_ADD_WIDTH-1:0]         s_ext_rx_tcdm_add;
   logic [TRANS_SID_WIDTH-1:0]        s_tcdm_tx_sid, s_tcdm_rx_sid, s_ext_tx_sid, s_ext_rx_sid;
   
   logic [1:0]                        s_tx_data_push_req, s_tx_data_push_gnt, s_rx_data_pop_req, s_rx_data_pop_gnt;
   logic [1:0][31:0]                  s_tx_data_push_dat, s_rx_data_pop_dat;
   logic                              s_rx_data_push_gnt, s_tx_data_pop_req, s_rx_data_push_req, s_tx_data_pop_gnt;
   logic [7:0]                        s_tx_data_pop_strb;
   logic [1:0][3:0]                   s_rx_data_pop_strb;
   
   logic [63:0]                       s_rx_data_push_dat, s_tx_data_pop_dat;
   
   logic [2:0]                        s_trans_tx_ext_add, s_trans_rx_ext_add;
   logic [2:0]                        s_trans_tx_tcdm_add, s_trans_rx_tcdm_add;
   logic [MCHAN_LEN_WIDTH-1:0]        s_trans_tx_len, s_trans_rx_len;
   logic                              s_trans_tx_req, s_trans_rx_req;
   logic                              s_trans_tx_gnt, s_trans_rx_gnt;
   
   logic                              s_tx_tcdm_synch_req, s_rx_tcdm_synch_req, s_tx_ext_synch_req, s_rx_ext_synch_req;
   logic [TRANS_SID_WIDTH-1:0]        s_tx_tcdm_synch_sid, s_rx_tcdm_synch_sid, s_tx_ext_synch_sid, s_rx_ext_synch_sid;
   
   //**********************************************************
   //*************** CTRL UNIT ********************************
   //**********************************************************
   
   ctrl_unit
     #(
       .NB_CTRLS                 ( NB_CTRLS                 ),
       .NB_TRANSFERS             ( NB_TRANSFERS             ),
       .CTRL_TRANS_QUEUE_DEPTH   ( CTRL_TRANS_QUEUE_DEPTH   ),
       .GLOBAL_TRANS_QUEUE_DEPTH ( GLOBAL_TRANS_QUEUE_DEPTH ),
       .TWD_QUEUE_DEPTH          ( TWD_QUEUE_DEPTH          ),
       .TCDM_ADD_WIDTH           ( TCDM_ADD_WIDTH           ),
       .EXT_ADD_WIDTH            ( EXT_ADD_WIDTH            ),
       .TRANS_SID_WIDTH          ( TRANS_SID_WIDTH          ),
       .MCHAN_BURST_LENGTH       ( MCHAN_BURST_LENGTH       ),
       .PE_ID_WIDTH              ( PE_ID_WIDTH              )
       )
   ctrl_unit_i
     (
      
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .test_mode_i(test_mode_i),
      
      .clk_gated_o(s_clk_gated),
      
      .ctrl_targ_req_i(ctrl_targ_req_i),
      .ctrl_targ_add_i(ctrl_targ_add_i),
      .ctrl_targ_type_i(ctrl_targ_type_i),
      .ctrl_targ_be_i (ctrl_targ_be_i),
      .ctrl_targ_data_i(ctrl_targ_data_i),
      .ctrl_targ_id_i(ctrl_targ_id_i),
      .ctrl_targ_gnt_o(ctrl_targ_gnt_o),
      
      .ctrl_targ_r_valid_o(ctrl_targ_r_valid_o),
      .ctrl_targ_r_data_o(ctrl_targ_r_data_o),
      .ctrl_targ_r_opc_o(ctrl_targ_r_opc_o),
      .ctrl_targ_r_id_o(ctrl_targ_r_id_o),
      
      .tcdm_tx_sid_o(s_tcdm_tx_sid),
      .tcdm_tx_add_o(s_tcdm_tx_add),
      .tcdm_tx_opc_o(s_tcdm_tx_opc),
      .tcdm_tx_len_o(s_tcdm_tx_len),
      .tcdm_tx_req_o(s_tcdm_tx_req),
      .tcdm_tx_gnt_i(s_tcdm_tx_gnt),
      
      .ext_tx_sid_o(s_ext_tx_sid),
      .ext_tx_add_o(s_ext_tx_add),
      .ext_tx_opc_o(s_ext_tx_opc),
      .ext_tx_len_o(s_ext_tx_len),
      .ext_tx_req_o(s_ext_tx_req),
      .ext_tx_bst_o(s_ext_tx_bst),
      .ext_tx_gnt_i(s_ext_tx_gnt),
      
      .ext_rx_sid_o(s_ext_rx_sid),
      .ext_rx_add_o(s_ext_rx_add),
      .ext_rx_tcdm_add_o(s_ext_rx_tcdm_add),
      .ext_rx_opc_o(s_ext_rx_opc),
      .ext_rx_len_o(s_ext_rx_len),
      .ext_rx_bst_o(s_ext_rx_bst),
      .ext_rx_req_o(s_ext_rx_req),
      .ext_rx_gnt_i(s_ext_rx_gnt),
      
      .trans_tx_ext_add_o(s_trans_tx_ext_add),
      .trans_tx_tcdm_add_o(s_trans_tx_tcdm_add),
      .trans_tx_len_o(s_trans_tx_len),
      .trans_tx_req_o(s_trans_tx_req),
      .trans_tx_gnt_i(s_trans_tx_gnt),
      
      .tcdm_tx_synch_req_i(s_tx_tcdm_synch_req),
      .tcdm_tx_synch_sid_i(s_tx_tcdm_synch_sid),
      
      .tcdm_rx_synch_req_i(s_rx_tcdm_synch_req),
      .tcdm_rx_synch_sid_i(s_rx_tcdm_synch_sid),
      
      .ext_tx_synch_req_i(s_tx_ext_synch_req),
      .ext_tx_synch_sid_i(s_tx_ext_synch_sid),
      
      .ext_rx_synch_req_i(s_rx_ext_synch_req),
      .ext_rx_synch_sid_i(s_rx_ext_synch_sid),
      
      .term_evt_o(term_evt_o),
      .term_int_o(term_int_o),
      
      .busy_o(busy_o)
      
      );
   
   //**********************************************************
   //*************** EXTRENAL MODULE **************************
   //**********************************************************
   
   ext_unit
     #(
       .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
       .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
       .AXI_USER_WIDTH(AXI_USER_WIDTH),
       .AXI_ID_WIDTH(AXI_ID_WIDTH),
       .AXI_STRB_WIDTH(AXI_STRB_WIDTH),
       .TRANS_SID_WIDTH(TRANS_SID_WIDTH),
       .EXT_ADD_WIDTH(EXT_ADD_WIDTH),
       .EXT_OPC_WIDTH(EXT_OPC_WIDTH),
       .EXT_TID_WIDTH(EXT_TID_WIDTH),
       .TCDM_ADD_WIDTH(TCDM_ADD_WIDTH),
       .TCDM_OPC_WIDTH(TCDM_OPC_WIDTH),
       .MCHAN_LEN_WIDTH(MCHAN_LEN_WIDTH)
       )
   ext_unit_i
     (
      
      .clk_i(s_clk_gated),
      .rst_ni(rst_ni),

      .test_mode_i(test_mode_i),
      
      .axi_master_aw_valid_o(axi_master_aw_valid_o),
      .axi_master_aw_addr_o(axi_master_aw_addr_o),
      .axi_master_aw_prot_o(axi_master_aw_prot_o),
      .axi_master_aw_region_o(axi_master_aw_region_o),
      .axi_master_aw_len_o(axi_master_aw_len_o),
      .axi_master_aw_size_o(axi_master_aw_size_o),
      .axi_master_aw_burst_o(axi_master_aw_burst_o),
      .axi_master_aw_lock_o(axi_master_aw_lock_o),
      .axi_master_aw_cache_o(axi_master_aw_cache_o),
      .axi_master_aw_qos_o(axi_master_aw_qos_o),
      .axi_master_aw_id_o(axi_master_aw_id_o),
      .axi_master_aw_user_o(axi_master_aw_user_o),
      .axi_master_aw_ready_i(axi_master_aw_ready_i),
      
      .axi_master_ar_valid_o(axi_master_ar_valid_o),
      .axi_master_ar_addr_o(axi_master_ar_addr_o),
      .axi_master_ar_prot_o(axi_master_ar_prot_o),
      .axi_master_ar_region_o(axi_master_ar_region_o),
      .axi_master_ar_len_o(axi_master_ar_len_o),
      .axi_master_ar_size_o(axi_master_ar_size_o),
      .axi_master_ar_burst_o(axi_master_ar_burst_o),
      .axi_master_ar_lock_o(axi_master_ar_lock_o),
      .axi_master_ar_cache_o(axi_master_ar_cache_o),
      .axi_master_ar_qos_o(axi_master_ar_qos_o),
      .axi_master_ar_id_o(axi_master_ar_id_o),
      .axi_master_ar_user_o(axi_master_ar_user_o),
      .axi_master_ar_ready_i(axi_master_ar_ready_i),
      
      .axi_master_w_valid_o(axi_master_w_valid_o),
      .axi_master_w_data_o(axi_master_w_data_o),
      .axi_master_w_strb_o(axi_master_w_strb_o),
      .axi_master_w_user_o(axi_master_w_user_o),
      .axi_master_w_last_o(axi_master_w_last_o),
      .axi_master_w_ready_i(axi_master_w_ready_i),
      
      .axi_master_r_valid_i(axi_master_r_valid_i),
      .axi_master_r_data_i(axi_master_r_data_i),
      .axi_master_r_resp_i(axi_master_r_resp_i),
      .axi_master_r_last_i(axi_master_r_last_i),
      .axi_master_r_id_i(axi_master_r_id_i),
      .axi_master_r_user_i(axi_master_r_user_i),
      .axi_master_r_ready_o(axi_master_r_ready_o),
      
      .axi_master_b_valid_i(axi_master_b_valid_i),
      .axi_master_b_resp_i(axi_master_b_resp_i),
      .axi_master_b_id_i(axi_master_b_id_i),
      .axi_master_b_user_i(axi_master_b_user_i),
      .axi_master_b_ready_o(axi_master_b_ready_o),
      
      .ext_rx_sid_i(s_ext_rx_sid),
      .ext_rx_add_i(s_ext_rx_add),
      .ext_rx_r_add_i(s_ext_rx_tcdm_add),
      .ext_rx_opc_i(s_ext_rx_opc),
      .ext_rx_len_i(s_ext_rx_len),
      .ext_rx_bst_i(s_ext_rx_bst),
      .ext_rx_req_i(s_ext_rx_req),
      .ext_rx_gnt_o(s_ext_rx_gnt),
      
      .ext_tx_sid_i(s_ext_tx_sid),
      .ext_tx_add_i(s_ext_tx_add),
      .ext_tx_opc_i(s_ext_tx_opc),
      .ext_tx_len_i(s_ext_tx_len),
      .ext_tx_bst_i(s_ext_tx_bst),
      .ext_tx_req_i(s_ext_tx_req),
      .ext_tx_gnt_o(s_ext_tx_gnt),
      
      .tcdm_rx_sid_o(s_tcdm_rx_sid),
      .tcdm_rx_add_o(s_tcdm_rx_add),
      .tcdm_rx_opc_o(s_tcdm_rx_opc),
      .tcdm_rx_len_o(s_tcdm_rx_len),
      .tcdm_rx_req_o(s_tcdm_rx_req),
      .tcdm_rx_gnt_i(s_tcdm_rx_gnt),
      
      .trans_rx_ext_add_o(s_trans_rx_ext_add),
      .trans_rx_tcdm_add_o(s_trans_rx_tcdm_add),
      .trans_rx_len_o(s_trans_rx_len),
      .trans_rx_req_o(s_trans_rx_req),
      .trans_rx_gnt_i(s_trans_rx_gnt),
      
      .tx_synch_req_o(s_tx_ext_synch_req),
      .tx_synch_sid_o(s_tx_ext_synch_sid),
      
      .rx_synch_req_o(s_rx_ext_synch_req),
      .rx_synch_sid_o(s_rx_ext_synch_sid),
      
      .tx_data_dat_i(s_tx_data_pop_dat),
      .tx_data_strb_i(s_tx_data_pop_strb),
      .tx_data_req_o(s_tx_data_pop_req),
      .tx_data_gnt_i(s_tx_data_pop_gnt),
      
      .rx_data_dat_o(s_rx_data_push_dat),
      .rx_data_req_o(s_rx_data_push_req),
      .rx_data_gnt_i(s_rx_data_push_gnt)
      
      );
   
   //**********************************************************
   //*************** TCDM UNIT ********************************
   //**********************************************************
   
   tcdm_unit
   #(
       .TRANS_SID_WIDTH(TRANS_SID_WIDTH),
       .TCDM_ADD_WIDTH(TCDM_ADD_WIDTH),
       .TCDM_OPC_WIDTH(TCDM_OPC_WIDTH),
       .MCHAN_LEN_WIDTH(MCHAN_LEN_WIDTH)
   )
   tcdm_unit_i
   (
      
      .clk_i(s_clk_gated),
      .rst_ni(rst_ni),

      .test_mode_i(test_mode_i),
      
      .tcdm_req_o(tcdm_init_req_o),
      .tcdm_add_o(tcdm_init_add_o),
      .tcdm_we_o(tcdm_init_type_o),
      .tcdm_be_o(tcdm_init_be_o),
      .tcdm_wdata_o(tcdm_init_data_o),
      .tcdm_sid_o(tcdm_init_sid_o),
      .tcdm_gnt_i(tcdm_init_gnt_i),
      .tcdm_r_valid_i(tcdm_init_r_valid_i),
      .tcdm_r_rdata_i(tcdm_init_r_data_i),
      
      .tcdm_tx_sid_i(s_tcdm_tx_sid),
      .tcdm_tx_add_i(s_tcdm_tx_add),
      .tcdm_tx_opc_i(s_tcdm_tx_opc),
      .tcdm_tx_len_i(s_tcdm_tx_len),
      .tcdm_tx_req_i(s_tcdm_tx_req),
      .tcdm_tx_gnt_o(s_tcdm_tx_gnt),
      
      .tcdm_rx_sid_i(s_tcdm_rx_sid),
      .tcdm_rx_add_i(s_tcdm_rx_add),
      .tcdm_rx_opc_i(s_tcdm_rx_opc),
      .tcdm_rx_len_i(s_tcdm_rx_len),
      .tcdm_rx_req_i(s_tcdm_rx_req),
      .tcdm_rx_gnt_o(s_tcdm_rx_gnt),
      
      .tx_data_dat_o(s_tx_data_push_dat),
      .tx_data_req_o(s_tx_data_push_req),
      .tx_data_gnt_i(s_tx_data_push_gnt),
      
      .rx_data_dat_i(s_rx_data_pop_dat),
      .rx_data_strb_i(s_rx_data_pop_strb),
      .rx_data_req_o(s_rx_data_pop_req),
      .rx_data_gnt_i(s_rx_data_pop_gnt),
      
      .tx_synch_req_o(s_tx_tcdm_synch_req),
      .tx_synch_sid_o(s_tx_tcdm_synch_sid),
      
      .rx_synch_req_o(s_rx_tcdm_synch_req),
      .rx_synch_sid_o(s_rx_tcdm_synch_sid)
      
    );
   
   //**********************************************************
   //*************** TRANSACTIONS BUFFER **********************
   //**********************************************************
   
   trans_unit
     #(
       .MCHAN_LEN_WIDTH(MCHAN_LEN_WIDTH)
       )
   trans_unit_i
     (
      
      .clk_i(s_clk_gated),
      .rst_ni(rst_ni),
      
      .test_mode_i(test_mode_i),

      .tx_trans_ext_addr_i(s_trans_tx_ext_add),
      .tx_trans_tcdm_addr_i(s_trans_tx_tcdm_add),
      .tx_trans_len_i(s_trans_tx_len),
      .tx_trans_req_i(s_trans_tx_req),
      .tx_trans_gnt_o(s_trans_tx_gnt),
      
      .rx_trans_tcdm_addr_i(s_trans_rx_tcdm_add),
      .rx_trans_ext_addr_i(s_trans_rx_ext_add),
      .rx_trans_len_i(s_trans_rx_len),
      .rx_trans_req_i(s_trans_rx_req),
      .rx_trans_gnt_o(s_trans_rx_gnt),
      
      .tx_data_push_dat_i(s_tx_data_push_dat),
      .tx_data_push_req_i(s_tx_data_push_req),
      .tx_data_push_gnt_o(s_tx_data_push_gnt),
      
      .tx_data_pop_dat_o(s_tx_data_pop_dat),
      .tx_data_pop_strb_o(s_tx_data_pop_strb),
      .tx_data_pop_req_i(s_tx_data_pop_req),
      .tx_data_pop_gnt_o(s_tx_data_pop_gnt),
      
      .rx_data_push_dat_i(s_rx_data_push_dat),
      .rx_data_push_req_i(s_rx_data_push_req),
      .rx_data_push_gnt_o(s_rx_data_push_gnt),
      
      .rx_data_pop_dat_o(s_rx_data_pop_dat),
      .rx_data_pop_strb_o(s_rx_data_pop_strb),
      .rx_data_pop_req_i(s_rx_data_pop_req),
      .rx_data_pop_gnt_o(s_rx_data_pop_gnt)
      
      );
   
endmodule
