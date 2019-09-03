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

module ctrl_unit
  #(
    // OVERRIDDEN FROM TOP
    parameter NB_CORES                 = 4,
    parameter NB_TRANSFERS             = 4,
    parameter CORE_TRANS_QUEUE_DEPTH   = 2,
    parameter GLOBAL_TRANS_QUEUE_DEPTH = 8,
    parameter TWD_QUEUE_DEPTH          = 4,
    parameter TCDM_ADD_WIDTH           = 16,
    parameter EXT_ADD_WIDTH            = 32,
    parameter MCHAN_BURST_LENGTH       = 64,
    parameter PE_ID_WIDTH              = 1,
    // DEFINED IN MINICHAN_DEFINES
    parameter MCHAN_OPC_WIDTH          = `MCHAN_OPC_WIDTH,
    parameter MCHAN_LEN_WIDTH          = `MCHAN_LEN_WIDTH,
    parameter TCDM_OPC_WIDTH           = `TCDM_OPC_WIDTH,
    parameter EXT_OPC_WIDTH            = `EXT_OPC_WIDTH,
    parameter TWD_COUNT_WIDTH          = `TWD_COUNT_WIDTH,
    parameter TWD_STRIDE_WIDTH         = `TWD_STRIDE_WIDTH,
    // DERIVED
    parameter TWD_QUEUE_WIDTH          = TWD_COUNT_WIDTH+TWD_STRIDE_WIDTH,
    parameter TRANS_CID_WIDTH          = $clog2(NB_CORES)+1,
    parameter TRANS_SID_WIDTH          = $clog2(NB_TRANSFERS),
    parameter TWD_QUEUE_ADD_WIDTH      = $clog2(TWD_QUEUE_DEPTH)
    )
   (
    
    input  logic                        clk_i,
    input  logic                        rst_ni,
    
    input  logic                        test_mode_i,
    
    output logic                        clk_gated_o,
    
    // CONTROL TARGET PE
    //***************************************
    input  logic                        ctrl_pe_targ_req_i,
    input  logic                        ctrl_pe_targ_type_i,
    input  logic [3:0]                  ctrl_pe_targ_be_i,
    input  logic [31:0]                 ctrl_pe_targ_add_i,
    input  logic [31:0]                 ctrl_pe_targ_data_i,
    input  logic [PE_ID_WIDTH-1:0]      ctrl_pe_targ_id_i,
    output logic                        ctrl_pe_targ_gnt_o,
    
    output logic                        ctrl_pe_targ_r_valid_o,
    output logic [31:0]                 ctrl_pe_targ_r_data_o,
    output logic                        ctrl_pe_targ_r_opc_o,
    output logic [PE_ID_WIDTH-1:0]      ctrl_pe_targ_r_id_o,
    
    // CONTROL TARGET
    //***************************************
    input  logic [NB_CORES-1:0]         ctrl_targ_req_i,
    input  logic [NB_CORES-1:0]         ctrl_targ_type_i,
    input  logic [NB_CORES-1:0][3:0]    ctrl_targ_be_i,
    input  logic [NB_CORES-1:0][31:0]   ctrl_targ_add_i,
    input  logic [NB_CORES-1:0][31:0]   ctrl_targ_data_i,
    output logic [NB_CORES-1:0]         ctrl_targ_gnt_o,
    
    output logic [NB_CORES-1:0]         ctrl_targ_r_valid_o,
    output logic [NB_CORES-1:0][31:0]   ctrl_targ_r_data_o,
    
    // CMD QUEUES
    //***************************************
    output logic [TRANS_SID_WIDTH-1:0]  tcdm_tx_sid_o,
    output logic [TCDM_ADD_WIDTH-1:0]   tcdm_tx_add_o,
    output logic [TCDM_OPC_WIDTH-1:0]   tcdm_tx_opc_o,
    output logic [MCHAN_LEN_WIDTH-1:0]  tcdm_tx_len_o,
    output logic                        tcdm_tx_req_o,
    input  logic                        tcdm_tx_gnt_i,
    
    output logic [TRANS_SID_WIDTH-1:0]  ext_tx_sid_o,
    output logic [EXT_ADD_WIDTH-1:0]    ext_tx_add_o,
    output logic [EXT_OPC_WIDTH-1:0]    ext_tx_opc_o,
    output logic [MCHAN_LEN_WIDTH-1:0]  ext_tx_len_o,
    output logic                        ext_tx_bst_o,
    output logic                        ext_tx_req_o,
    input  logic                        ext_tx_gnt_i,
    
    output logic [TRANS_SID_WIDTH-1:0]  ext_rx_sid_o,
    output logic [EXT_ADD_WIDTH-1:0]    ext_rx_add_o,
    output logic [TCDM_ADD_WIDTH-1:0]   ext_rx_tcdm_add_o,
    output logic [EXT_OPC_WIDTH-1:0]    ext_rx_opc_o,
    output logic [MCHAN_LEN_WIDTH-1:0]  ext_rx_len_o,
    output logic                        ext_rx_bst_o,
    output logic                        ext_rx_req_o,
    input  logic                        ext_rx_gnt_i,
    
    // TRANS UNIT
    output logic [2:0]                  trans_tx_ext_add_o,
    output logic [2:0]                  trans_tx_tcdm_add_o,
    output logic [MCHAN_LEN_WIDTH-1:0]  trans_tx_len_o,
    output logic                        trans_tx_req_o,
    input  logic                        trans_tx_gnt_i,
    
    // SYNCHRONIZATION
    //***************************************
    input  logic                        tcdm_tx_synch_req_i,
    input  logic [TRANS_SID_WIDTH-1:0]  tcdm_tx_synch_sid_i,
    
    input  logic                        tcdm_rx_synch_req_i,
    input  logic [TRANS_SID_WIDTH-1:0]  tcdm_rx_synch_sid_i,
    
    input  logic                        ext_tx_synch_req_i,
    input  logic [TRANS_SID_WIDTH-1:0]  ext_tx_synch_sid_i,
    
    input  logic                        ext_rx_synch_req_i,
    input  logic [TRANS_SID_WIDTH-1:0]  ext_rx_synch_sid_i,
    
    // TERMINATION EVENTS AND INTERRUPTS
    //**************************************
    output logic [NB_CORES:0]           term_evt_o,
    output logic [NB_CORES:0]           term_int_o,
    
    // BUSY SIGNAL
    //***************************************
    output logic                        busy_o
    );
   
   // LOCAL PARAMETERS
   localparam TRANS_ARBITER_WIDTH    = MCHAN_OPC_WIDTH + MCHAN_LEN_WIDTH + TCDM_ADD_WIDTH + EXT_ADD_WIDTH + TRANS_SID_WIDTH + TWD_QUEUE_ADD_WIDTH + 5; // INC, TWD, ELE, ILE, BLE
   localparam TRANS_QUEUE_WIDTH      = MCHAN_OPC_WIDTH + MCHAN_LEN_WIDTH + TCDM_ADD_WIDTH + EXT_ADD_WIDTH + TRANS_SID_WIDTH + TWD_QUEUE_ADD_WIDTH + 2; // INC, TWD
   localparam EXT_RX_CMD_QUEUE_WIDTH = MCHAN_OPC_WIDTH + MCHAN_LEN_WIDTH + TCDM_ADD_WIDTH + EXT_ADD_WIDTH + TRANS_SID_WIDTH + 1; // INC
   localparam EXT_TX_CMD_QUEUE_WIDTH = MCHAN_OPC_WIDTH + MCHAN_LEN_WIDTH + TCDM_ADD_WIDTH + EXT_ADD_WIDTH + TRANS_SID_WIDTH + 1; // INC

   // SIGNALS FROM CORE INTERFACE (INDLUDE PE INTERFACE)
   logic [NB_CORES:0]			           s_trans_alloc_req;
   logic [NB_CORES:0] 				   s_trans_alloc_gnt;
   logic [NB_CORES:0][TRANS_SID_WIDTH-1:0] 	   s_trans_alloc_ret;
   logic [NB_CORES:0][NB_TRANSFERS-1:0] 	   s_trans_alloc_clr;
   logic [NB_CORES:0][NB_TRANSFERS-1:0] 	   s_trans_alloc_status;
   
   logic [NB_CORES:0] 				   s_core_req;
   logic [NB_CORES:0] 				   s_core_gnt;
   logic [NB_CORES:0][MCHAN_LEN_WIDTH-1:0] 	   s_core_len;
   logic [NB_CORES:0][MCHAN_OPC_WIDTH-1:0] 	   s_core_opc;
   logic [NB_CORES:0] 				   s_core_inc;
   logic [NB_CORES:0] 				   s_core_twd;
   logic [NB_CORES:0] 				   s_core_ele;
   logic [NB_CORES:0] 				   s_core_ile;
   logic [NB_CORES:0] 				   s_core_ble;
   logic [NB_CORES:0][TWD_QUEUE_ADD_WIDTH-1:0] 	   s_core_twd_add;
   logic [NB_CORES:0][TRANS_SID_WIDTH-1:0] 	   s_core_sid;
   logic [NB_CORES:0][TCDM_ADD_WIDTH-1:0] 	   s_core_tcdm_add;
   logic [NB_CORES:0][EXT_ADD_WIDTH-1:0] 	   s_core_ext_add;
   
   logic [NB_CORES:0] 				   s_twd_alloc_req;
   logic [NB_CORES:0] 				   s_twd_alloc_gnt;
   logic [NB_CORES:0][TWD_QUEUE_ADD_WIDTH-1:0] 	   s_twd_alloc_add;
   
   logic [NB_CORES:0] 				   s_twd_queue_req;
   logic [NB_CORES:0][TWD_QUEUE_ADD_WIDTH-1:0]     s_twd_queue_add;
   logic [NB_CORES:0][TWD_QUEUE_WIDTH-1:0] 	   s_twd_queue_dat;
   logic [NB_CORES:0][TRANS_SID_WIDTH-1:0] 	   s_twd_queue_sid;
   
   logic [NB_CORES:0] 				   s_cores_busy;
   
   logic [MCHAN_LEN_WIDTH-1:0] 			   s_arb_len;
   logic [MCHAN_OPC_WIDTH-1:0] 			   s_arb_opc;
   logic 					   s_arb_inc;
   logic 					   s_arb_twd;
   logic 					   s_arb_ele;
   logic 					   s_arb_ile;
   logic 					   s_arb_ble;
   logic [TWD_QUEUE_ADD_WIDTH-1:0] 		   s_arb_twd_add;
   logic [TRANS_SID_WIDTH-1:0] 			   s_arb_sid;
   logic [TCDM_ADD_WIDTH-1:0] 			   s_arb_tcdm_add;
   logic [EXT_ADD_WIDTH-1:0] 			   s_arb_ext_add;
   logic [TRANS_CID_WIDTH-1:0]                     s_arb_cid;
   logic                                           s_arb_req;
   logic                                           s_arb_gnt;
   
   logic [MCHAN_OPC_WIDTH-1:0]                     s_tx_opc,s_rx_opc;
   logic [MCHAN_LEN_WIDTH-1:0]                     s_tx_len,s_rx_len;
   logic [TRANS_SID_WIDTH-1:0]                     s_tx_sid,s_rx_sid;
   logic [TCDM_ADD_WIDTH-1:0]                      s_tx_tcdm_add,s_rx_tcdm_add;
   logic [EXT_ADD_WIDTH-1:0]                       s_tx_ext_add,s_rx_ext_add;
   logic                                           s_tx_twd,s_rx_twd;
   logic [TWD_COUNT_WIDTH-1:0]			   s_tx_count,s_rx_count;
   logic [TWD_STRIDE_WIDTH-1:0]			   s_tx_stride,s_rx_stride;
   logic [TWD_QUEUE_ADD_WIDTH-1:0]                 s_tx_twd_add,s_rx_twd_add;
   logic                                           s_tx_inc,s_rx_inc;
   logic                                           s_tx_req,s_rx_req;
   logic                                           s_tx_gnt,s_rx_gnt;
   
   logic 					   s_tx_split_req,s_rx_split_req;
   logic 					   s_tx_split_gnt,s_rx_split_gnt;
   logic [TRANS_SID_WIDTH-1:0] 			   s_tx_split_sid,s_rx_split_sid;
   logic 					   s_tx_split_opc,s_rx_split_opc;
   logic [MCHAN_LEN_WIDTH-1:0] 			   s_tx_split_len,s_rx_split_len;
   logic 					   s_tx_split_inc,s_rx_split_inc;
   logic [TCDM_ADD_WIDTH-1:0] 			   s_tx_split_tcdm_add,s_rx_split_tcdm_add;
   logic [EXT_ADD_WIDTH-1:0] 			   s_tx_split_ext_add,s_rx_split_ext_add;
   
   logic 					   s_tx_queue_req,s_rx_queue_req;
   logic 					   s_tx_queue_gnt,s_rx_queue_gnt;
   logic [TRANS_SID_WIDTH-1:0] 			   s_tx_queue_sid,s_rx_queue_sid;
   logic 					   s_tx_queue_opc,s_rx_queue_opc;
   logic [MCHAN_LEN_WIDTH-1:0] 			   s_tx_queue_len,s_rx_queue_len;
   logic 					   s_tx_queue_inc,s_rx_queue_inc;
   logic [TCDM_ADD_WIDTH-1:0] 			   s_tx_queue_tcdm_add,s_rx_queue_tcdm_add;
   logic [EXT_ADD_WIDTH-1:0] 			   s_tx_queue_ext_add,s_rx_queue_ext_add;
   
   logic [NB_TRANSFERS-1:0] 			   s_trans_status;
   
   logic [NB_TRANSFERS-1:0] 			   s_term_sig;
   
   genvar                                          i;
   
   //**********************************************************
   //*************** MCHAN CORES INTERFACE ********************
   //**********************************************************
   
   core_if_pe
     #(
       .NB_TRANSFERS           ( NB_TRANSFERS           ),
       .TWD_QUEUE_DEPTH        ( TWD_QUEUE_DEPTH        ),
       .CORE_TRANS_QUEUE_DEPTH ( CORE_TRANS_QUEUE_DEPTH ),
       .TCDM_ADD_WIDTH         ( TCDM_ADD_WIDTH         ),
       .EXT_ADD_WIDTH          ( EXT_ADD_WIDTH          ),
       .TRANS_SID_WIDTH        ( TRANS_SID_WIDTH        ),
       .TWD_COUNT_WIDTH        ( TWD_COUNT_WIDTH        ),
       .TWD_STRIDE_WIDTH       ( TWD_STRIDE_WIDTH       ),
       .TWD_QUEUE_WIDTH        ( TWD_QUEUE_WIDTH        ),
       .PE_ID_WIDTH            ( PE_ID_WIDTH            )
       )
   core_if_pe_i
     (
      .clk_i                ( clk_i                          ),
      .rst_ni               ( rst_ni                         ),
      
      .test_mode_i          ( test_mode_i                    ),
      
      .ctrl_targ_req_i      ( ctrl_pe_targ_req_i             ),
      .ctrl_targ_add_i      ( ctrl_pe_targ_add_i             ),
      .ctrl_targ_type_i     ( ctrl_pe_targ_type_i            ),
      .ctrl_targ_be_i       ( ctrl_pe_targ_be_i              ),
      .ctrl_targ_data_i     ( ctrl_pe_targ_data_i            ),
      .ctrl_targ_id_i       ( ctrl_pe_targ_id_i              ),
      .ctrl_targ_gnt_o      ( ctrl_pe_targ_gnt_o             ),
      
      .ctrl_targ_r_valid_o  ( ctrl_pe_targ_r_valid_o         ),
      .ctrl_targ_r_data_o   ( ctrl_pe_targ_r_data_o          ),
      .ctrl_targ_r_opc_o    ( ctrl_pe_targ_r_opc_o           ),
      .ctrl_targ_r_id_o     ( ctrl_pe_targ_r_id_o            ),
      
      .trans_alloc_req_o    ( s_trans_alloc_req[NB_CORES]    ),
      .trans_alloc_gnt_i    ( s_trans_alloc_gnt[NB_CORES]    ),
      .trans_alloc_ret_i    ( s_trans_alloc_ret[NB_CORES]    ),
      .trans_alloc_clr_o    ( s_trans_alloc_clr[NB_CORES]    ),
      .trans_alloc_status_i ( s_trans_alloc_status[NB_CORES] ),
      
      .cmd_req_o            ( s_core_req[NB_CORES]           ),
      .cmd_gnt_i            ( s_core_gnt[NB_CORES]           ),
      .cmd_len_o            ( s_core_len[NB_CORES]           ),
      .cmd_opc_o            ( s_core_opc[NB_CORES]           ),
      .cmd_inc_o            ( s_core_inc[NB_CORES]           ),
      .cmd_twd_o            ( s_core_twd[NB_CORES]           ),
      .cmd_ele_o            ( s_core_ele[NB_CORES]           ),
      .cmd_ile_o            ( s_core_ile[NB_CORES]           ),
      .cmd_ble_o            ( s_core_ble[NB_CORES]           ),
      .cmd_twd_add_o        ( s_core_twd_add[NB_CORES]       ),
      .cmd_sid_o            ( s_core_sid[NB_CORES]           ),
      .tcdm_add_o           ( s_core_tcdm_add[NB_CORES]      ),
      .ext_add_o            ( s_core_ext_add[NB_CORES]       ),
      
      .twd_alloc_req_o      ( s_twd_alloc_req[NB_CORES]      ),
      .twd_alloc_gnt_i      ( s_twd_alloc_gnt[NB_CORES]      ),
      .twd_alloc_add_i      ( s_twd_alloc_add[NB_CORES]      ),
      
      .twd_queue_req_o      ( s_twd_queue_req[NB_CORES]      ),
      .twd_queue_add_o      ( s_twd_queue_add[NB_CORES]      ),
      .twd_queue_dat_o      ( s_twd_queue_dat[NB_CORES]      ),
      .twd_queue_sid_o      ( s_twd_queue_sid[NB_CORES]      ),

      .arb_gnt_i            ( s_arb_gnt                      ),
      .arb_req_i            ( s_arb_req                      ),
      .arb_sid_i            ( s_arb_sid                      ),
      
      .trans_status_i       ( s_trans_status                 ),
      
      .busy_o               ( s_cores_busy[NB_CORES]         )
      
      );
   
   generate
      
      for (i=0; i<NB_CORES; i++)
        begin : core_if_bind
           core_if
             #(
	       .NB_TRANSFERS           ( NB_TRANSFERS           ),
	       .TWD_QUEUE_DEPTH        ( TWD_QUEUE_DEPTH        ),
               .CORE_TRANS_QUEUE_DEPTH ( CORE_TRANS_QUEUE_DEPTH ),
               .TCDM_ADD_WIDTH         ( TCDM_ADD_WIDTH         ),
               .EXT_ADD_WIDTH          ( EXT_ADD_WIDTH          ),
               .TRANS_SID_WIDTH        ( TRANS_SID_WIDTH        ),
	       .TWD_COUNT_WIDTH        ( TWD_COUNT_WIDTH        ),
	       .TWD_STRIDE_WIDTH       ( TWD_STRIDE_WIDTH       ),
	       .TWD_QUEUE_WIDTH        ( TWD_QUEUE_WIDTH        )
               )
           core_if_i
             (
              .clk_i                ( clk_i                   ),
              .rst_ni               ( rst_ni                  ),
	      
	      .test_mode_i          ( test_mode_i             ),
              
              .ctrl_targ_req_i      ( ctrl_targ_req_i[i]      ),
              .ctrl_targ_add_i      ( ctrl_targ_add_i[i]      ),
              .ctrl_targ_type_i     ( ctrl_targ_type_i[i]     ),
              .ctrl_targ_be_i       ( ctrl_targ_be_i[i]       ),
              .ctrl_targ_data_i     ( ctrl_targ_data_i[i]     ),
              .ctrl_targ_gnt_o      ( ctrl_targ_gnt_o[i]      ),
              
              .ctrl_targ_r_valid_o  ( ctrl_targ_r_valid_o[i]  ),
              .ctrl_targ_r_data_o   ( ctrl_targ_r_data_o[i]   ),
	      
	      .trans_alloc_req_o    ( s_trans_alloc_req[i]    ),
	      .trans_alloc_gnt_i    ( s_trans_alloc_gnt[i]    ),
	      .trans_alloc_ret_i    ( s_trans_alloc_ret[i]    ),
              .trans_alloc_clr_o    ( s_trans_alloc_clr[i]    ),
	      .trans_alloc_status_i ( s_trans_alloc_status[i] ),
              
              .cmd_req_o            ( s_core_req[i]           ),
              .cmd_gnt_i            ( s_core_gnt[i]           ),
	      .cmd_len_o            ( s_core_len[i]           ),
	      .cmd_opc_o            ( s_core_opc[i]           ),
	      .cmd_inc_o            ( s_core_inc[i]           ),
	      .cmd_twd_o            ( s_core_twd[i]           ),
	      .cmd_ele_o            ( s_core_ele[i]           ),
	      .cmd_ile_o            ( s_core_ile[i]           ),
	      .cmd_ble_o            ( s_core_ble[i]           ),
	      .cmd_twd_add_o        ( s_core_twd_add[i]       ),
	      .cmd_sid_o            ( s_core_sid[i]           ),
	      .tcdm_add_o           ( s_core_tcdm_add[i]      ),
	      .ext_add_o            ( s_core_ext_add[i]       ),
	      
	      .twd_alloc_req_o      ( s_twd_alloc_req[i]      ),
	      .twd_alloc_gnt_i      ( s_twd_alloc_gnt[i]      ),
	      .twd_alloc_add_i      ( s_twd_alloc_add[i]      ),
	      
	      .twd_queue_req_o      ( s_twd_queue_req[i]      ),
	      .twd_queue_add_o      ( s_twd_queue_add[i]      ),
	      .twd_queue_dat_o      ( s_twd_queue_dat[i]      ),
	      .twd_queue_sid_o      ( s_twd_queue_sid[i]      ),

	      .arb_gnt_i            ( s_arb_gnt               ),
	      .arb_req_i            ( s_arb_req               ),
	      .arb_sid_i            ( s_arb_sid               ),
	      
	      .trans_status_i       ( s_trans_status          ),
              
              .busy_o               ( s_cores_busy[i]         )
              );
        end
      
   endgenerate
   
   //**********************************************************
   //*************** TRANSFERS ALLOCATOR **********************
   //**********************************************************
   
   trans_allocator
     #(
       .NB_CORES(NB_CORES),
       .NB_TRANSFERS(NB_TRANSFERS),
       .TRANS_SID_WIDTH(TRANS_SID_WIDTH),
       .TRANS_CID_WIDTH(TRANS_CID_WIDTH)
       )
   trans_allocator_i
     (
      .clk_i          ( clk_gated_o          ),
      .rst_ni         ( rst_ni               ),
      
      .trans_req_i    ( s_trans_alloc_req    ),
      .trans_gnt_o    ( s_trans_alloc_gnt    ),
      .trans_sid_o    ( s_trans_alloc_ret    ),
      .trans_sid_i    ( s_trans_alloc_clr    ),
      
      .trans_status_o ( s_trans_alloc_status ),
      
      .cmd_req_i      ( s_arb_req            ),
      .cmd_gnt_i      ( s_arb_gnt            ),
      .cmd_cid_i      ( s_arb_cid            ),
      .cmd_sid_i      ( s_arb_sid            ),
      .cmd_ele_i      ( s_arb_ele            ),
      .cmd_ile_i      ( s_arb_ile            ),
      .cmd_ble_i      ( s_arb_ble            ),
      
      // INPUT TERMINATION EVENTS
      .term_sig_i     ( s_term_sig           ),
      
      // BUFFERED OUTPUT TERMINATION EVENTS AND INTERRUPTS
      .term_evt_o     ( term_evt_o           ),
      .term_int_o     ( term_int_o           )
      );
   
   //**********************************************************
   //*************** SYNCHRONIZATION UNITS ********************
   //**********************************************************
   
   generate
      
      for (i=0; i<NB_TRANSFERS; i++)
        begin : synch_unit_bind
	   
	   synch_unit
	     #(
	       .NB_CORES(NB_CORES),
	       .TRANS_SID(i),
	       .TRANS_SID_WIDTH(TRANS_SID_WIDTH),
	       .TRANS_CID_WIDTH(TRANS_CID_WIDTH),
	       .EXT_ADD_WIDTH(EXT_ADD_WIDTH),
	       .MCHAN_BURST_LENGTH(MCHAN_BURST_LENGTH),
	       .TWD_COUNT_WIDTH(TWD_COUNT_WIDTH),
	       .TWD_STRIDE_WIDTH(TWD_STRIDE_WIDTH),
	       .TWD_QUEUE_WIDTH(TWD_QUEUE_WIDTH)
	       )
	   synch_unit_i
	     (
	      
	      .clk_i(clk_gated_o),
	      .rst_ni(rst_ni),
	      
	      .cmd_req_i(s_arb_req),
	      .cmd_gnt_i(s_arb_gnt),
	      .cmd_sid_i(s_arb_sid),
	      .cmd_len_i(s_arb_len),
	      .cmd_twd_i(s_arb_twd),
	      .ext_add_i(s_arb_ext_add),
	      
	      .twd_req_i(s_twd_queue_req),
	      .twd_dat_i(s_twd_queue_dat),
	      .twd_sid_i(s_twd_queue_sid),
	      
	      .tcdm_tx_synch_req_i(tcdm_tx_synch_req_i),
	      .tcdm_tx_synch_sid_i(tcdm_tx_synch_sid_i),
	      
	      .tcdm_rx_synch_req_i(tcdm_rx_synch_req_i),
	      .tcdm_rx_synch_sid_i(tcdm_rx_synch_sid_i),
	      
	      .ext_tx_synch_req_i(ext_tx_synch_req_i),
	      .ext_tx_synch_sid_i(ext_tx_synch_sid_i),
	      
	      .ext_rx_synch_req_i(ext_rx_synch_req_i),
	      .ext_rx_synch_sid_i(ext_rx_synch_sid_i),
	      
	      .trans_status_o(s_trans_status[i]),
	      
	      .term_sig_o(s_term_sig[i])
	      
	      );
	end
   endgenerate
   
   //**********************************************************
   //*************** ARBITER **********************************
   //**********************************************************
   
   trans_arbiter_wrap
     #(
       .DATA_WIDTH          ( TRANS_ARBITER_WIDTH ),
       .NB_CORES            ( NB_CORES            ),
       .MCHAN_LEN_WIDTH     ( MCHAN_LEN_WIDTH     ),
       .TCDM_ADD_WIDTH      ( TCDM_ADD_WIDTH      ),
       .EXT_ADD_WIDTH       ( EXT_ADD_WIDTH       ),
       .MCHAN_OPC_WIDTH     ( MCHAN_OPC_WIDTH     ),
       .TWD_QUEUE_ADD_WIDTH ( TWD_QUEUE_ADD_WIDTH ),
       .TRANS_SID_WIDTH     ( TRANS_SID_WIDTH     ),
       .TRANS_CID_WIDTH     ( TRANS_CID_WIDTH     )
       )
   trans_arbiter_i
     (
      
      .clk_i      ( clk_gated_o     ),
      .rst_ni     ( rst_ni          ),
      
      .req_i      ( s_core_req      ),
      .gnt_o      ( s_core_gnt      ),
      .len_i      ( s_core_len      ),
      .opc_i      ( s_core_opc      ),
      .inc_i      ( s_core_inc      ),
      .twd_i      ( s_core_twd      ),
      .ele_i      ( s_core_ele      ),
      .ile_i      ( s_core_ile      ),
      .ble_i      ( s_core_ble      ),
      .twd_add_i  ( s_core_twd_add  ),
      .sid_i      ( s_core_sid      ),
      .tcdm_add_i ( s_core_tcdm_add ),
      .ext_add_i  ( s_core_ext_add  ),
      
      .req_o      ( s_arb_req       ),
      .gnt_i      ( s_arb_gnt       ),
      .len_o      ( s_arb_len       ),
      .opc_o      ( s_arb_opc       ),
      .inc_o      ( s_arb_inc       ),
      .twd_o      ( s_arb_twd       ),
      .ele_o      ( s_arb_ele       ),
      .ile_o      ( s_arb_ile       ),
      .ble_o      ( s_arb_ble       ),
      .twd_add_o  ( s_arb_twd_add   ),
      .sid_o      ( s_arb_sid       ),
      .tcdm_add_o ( s_arb_tcdm_add  ),
      .ext_add_o  ( s_arb_ext_add   ),
      
      .cid_o      ( s_arb_cid       )
      
      );
   
   //**********************************************************
   //*************** TRANS QUEUE ******************************
   //**********************************************************
   
   trans_queue
     #(
       .TRANS_QUEUE_WIDTH  ( TRANS_QUEUE_WIDTH          ),
       .TRANS_QUEUE_DEPTH  ( GLOBAL_TRANS_QUEUE_DEPTH   ),
       .TCDM_ADD_WIDTH     ( TCDM_ADD_WIDTH             ),
       .EXT_ADD_WIDTH      ( EXT_ADD_WIDTH              ),
       .MCHAN_LEN_WIDTH    ( MCHAN_LEN_WIDTH            )
       )
   trans_queue_i
     (
      .clk_i     ( clk_gated_o                                              ),
      .rst_ni    ( rst_ni                                                   ),
      
      .req_i     ( s_arb_req                                                ),
      .gnt_o     ( s_arb_gnt                                                ),
      .dat_i     ( {s_arb_sid,s_arb_twd,s_arb_twd_add,s_arb_inc,s_arb_opc,s_arb_len,s_arb_tcdm_add,s_arb_ext_add} ),
      
      .tx_req_o  ( s_tx_req                                                 ),
      .tx_gnt_i  ( s_tx_gnt                                                 ),
      .tx_dat_o  ( {s_tx_sid,s_tx_twd,s_tx_twd_add,s_tx_inc,s_tx_opc,s_tx_len,s_tx_tcdm_add,s_tx_ext_add} ),
      
      .rx_req_o  ( s_rx_req                                                 ),
      .rx_gnt_i  ( s_rx_gnt                                                 ),
      .rx_dat_o  ( {s_rx_sid,s_rx_twd,s_rx_twd_add,s_rx_inc,s_rx_opc,s_rx_len,s_rx_tcdm_add,s_rx_ext_add} )
      );
   
   //**********************************************************
   //*************** 2D TRANS QUEUE ***************************
   //**********************************************************
   
   twd_trans_queue
     #(
       .NB_CORES(NB_CORES),
       .TWD_QUEUE_WIDTH(TWD_QUEUE_WIDTH),
       .TWD_QUEUE_DEPTH(TWD_QUEUE_DEPTH)
       )
   twd_trans_queue_i
     (
      .clk_i(clk_gated_o),
      .rst_ni(rst_ni),
      
      .alloc_req_i(s_twd_alloc_req),
      .alloc_gnt_o(s_twd_alloc_gnt),
      .alloc_add_o(s_twd_alloc_add),
      
      .wr_req_i(s_twd_queue_req),
      .wr_add_i(s_twd_queue_add),
      .wr_dat_i(s_twd_queue_dat),
      
      .tx_rd_req_i(s_tx_req & s_tx_gnt & s_tx_twd),
      .tx_rd_add_i(s_tx_twd_add),
      .tx_rd_dat_o({s_tx_stride,s_tx_count}),
      
      .rx_rd_req_i(s_rx_req & s_rx_gnt & s_rx_twd),
      .rx_rd_add_i(s_rx_twd_add),
      .rx_rd_dat_o({s_rx_stride,s_rx_count})
      );
   
   //**********************************************************
   //*************** 2D TRANS SPLITTER ************************
   //**********************************************************
   
   twd_trans_splitter
     #(
       .TRANS_SID_WIDTH    ( TRANS_SID_WIDTH    ),
       .TCDM_ADD_WIDTH     ( TCDM_ADD_WIDTH     ),
       .EXT_ADD_WIDTH      ( EXT_ADD_WIDTH      ),
       .MCHAN_BURST_LENGTH ( MCHAN_BURST_LENGTH ),
       .TWD_COUNT_WIDTH    ( TWD_COUNT_WIDTH    ),
       .TWD_STRIDE_WIDTH   ( TWD_STRIDE_WIDTH   )
       )
   tx_twd_trans_splitter_i
     (
      .clk_i(clk_gated_o),
      .rst_ni(rst_ni),
      
      .mchan_req_i         ( s_tx_req             ),
      .mchan_gnt_o         ( s_tx_gnt             ),
      .mchan_sid_i         ( s_tx_sid             ),
      .mchan_opc_i         ( s_tx_opc             ),
      .mchan_len_i         ( s_tx_len             ),
      .mchan_inc_i         ( s_tx_inc             ),
      .mchan_twd_i         ( s_tx_twd             ),
      .mchan_count_i       ( s_tx_count           ),
      .mchan_stride_i      ( s_tx_stride          ),
      .mchan_tcdm_add_i    ( s_tx_tcdm_add        ),
      .mchan_ext_add_i     ( s_tx_ext_add         ),
      
      .mchan_req_o         ( s_tx_split_req       ),
      .mchan_gnt_i         ( s_tx_split_gnt       ),
      .mchan_sid_o         ( s_tx_split_sid       ),
      .mchan_opc_o         ( s_tx_split_opc       ),
      .mchan_len_o         ( s_tx_split_len       ),
      .mchan_inc_o         ( s_tx_split_inc       ),
      .mchan_tcdm_add_o    ( s_tx_split_tcdm_add  ),
      .mchan_ext_add_o     ( s_tx_split_ext_add   )
      );
   
   twd_trans_splitter
     #(
       .TRANS_SID_WIDTH    ( TRANS_SID_WIDTH    ),
       .TCDM_ADD_WIDTH     ( TCDM_ADD_WIDTH     ),
       .EXT_ADD_WIDTH      ( EXT_ADD_WIDTH      ),
       .MCHAN_BURST_LENGTH ( MCHAN_BURST_LENGTH ),
       .TWD_COUNT_WIDTH    ( TWD_COUNT_WIDTH    ),
       .TWD_STRIDE_WIDTH   ( TWD_STRIDE_WIDTH   )
       )
   rx_twd_trans_splitter_i
     (
      .clk_i(clk_gated_o),
      .rst_ni(rst_ni),
      
      .mchan_req_i         ( s_rx_req             ),
      .mchan_gnt_o         ( s_rx_gnt             ),
      .mchan_sid_i         ( s_rx_sid             ),
      .mchan_opc_i         ( s_rx_opc             ),
      .mchan_len_i         ( s_rx_len             ),
      .mchan_inc_i         ( s_rx_inc             ),
      .mchan_twd_i         ( s_rx_twd             ),
      .mchan_count_i       ( s_rx_count           ),
      .mchan_stride_i      ( s_rx_stride          ),
      .mchan_tcdm_add_i    ( s_rx_tcdm_add        ),
      .mchan_ext_add_i     ( s_rx_ext_add         ),
      
      .mchan_req_o         ( s_rx_split_req       ),
      .mchan_gnt_i         ( s_rx_split_gnt       ),
      .mchan_sid_o         ( s_rx_split_sid       ),
      .mchan_opc_o         ( s_rx_split_opc       ),
      .mchan_len_o         ( s_rx_split_len       ),
      .mchan_inc_o         ( s_rx_split_inc       ),
      .mchan_tcdm_add_o    ( s_rx_split_tcdm_add  ),
      .mchan_ext_add_o     ( s_rx_split_ext_add   )
      );
   
   //**********************************************************
   //*************** TWD TRANS QUEUE **************************
   //**********************************************************
   
   mchan_fifo
     #(
       .DATA_WIDTH(EXT_TX_CMD_QUEUE_WIDTH),
       .DATA_DEPTH(2)
       )
   tx_trans_queue_i
     (
      .clk_i(clk_gated_o),
      .rst_ni(rst_ni),
      
      .push_dat_i({s_tx_split_sid,s_tx_split_inc,s_tx_split_opc,s_tx_split_len,s_tx_split_tcdm_add,s_tx_split_ext_add}),
      .push_req_i(s_tx_split_req),
      .push_gnt_o(s_tx_split_gnt),
      
      .pop_dat_o({s_tx_queue_sid,s_tx_queue_inc,s_tx_queue_opc,s_tx_queue_len,s_tx_queue_tcdm_add,s_tx_queue_ext_add}),
      .pop_req_i(s_tx_queue_gnt),
      .pop_gnt_o(s_tx_queue_req)
      );
   
   mchan_fifo
     #(
       .DATA_WIDTH(EXT_RX_CMD_QUEUE_WIDTH),
       .DATA_DEPTH(2)
       )
   rx_trans_queue_i
     (
      .clk_i(clk_gated_o),
      .rst_ni(rst_ni),
      
      .push_dat_i({s_rx_split_sid,s_rx_split_inc,s_rx_split_opc,s_rx_split_len,s_rx_split_tcdm_add,s_rx_split_ext_add}),
      .push_req_i(s_rx_split_req),
      .push_gnt_o(s_rx_split_gnt),
      
      .pop_dat_o({s_rx_queue_sid,s_rx_queue_inc,s_rx_queue_opc,s_rx_queue_len,s_rx_queue_tcdm_add,s_rx_queue_ext_add}),
      .pop_req_i(s_rx_queue_gnt),
      .pop_gnt_o(s_rx_queue_req)
      );
   
   //**********************************************************
   //*************** TRANS UNPACK *****************************
   //**********************************************************
   
   trans_unpack
    #(
      .TRANS_SID_WIDTH    ( TRANS_SID_WIDTH    ),
      .TCDM_ADD_WIDTH     ( TCDM_ADD_WIDTH     ),
      .EXT_ADD_WIDTH      ( EXT_ADD_WIDTH      ),
      .MCHAN_BURST_LENGTH ( MCHAN_BURST_LENGTH )
    )
    tx_trans_unpack_i
      (
       .clk_i               ( clk_gated_o          ),
       .rst_ni              ( rst_ni               ),
       
       .mchan_sid_i         ( s_tx_queue_sid       ),
       .mchan_opc_i         ( s_tx_queue_opc       ),
       .mchan_len_i         ( s_tx_queue_len       ),
       .mchan_inc_i         ( s_tx_queue_inc       ),
       .mchan_tcdm_add_i    ( s_tx_queue_tcdm_add  ),
       .mchan_ext_add_i     ( s_tx_queue_ext_add   ),
       .mchan_req_i         ( s_tx_queue_req       ),
       .mchan_gnt_o         ( s_tx_queue_gnt       ),
       
       .tcdm_sid_o          ( tcdm_tx_sid_o        ),
       .tcdm_opc_o          ( tcdm_tx_opc_o        ),
       .tcdm_len_o          ( tcdm_tx_len_o        ),
       .tcdm_add_o          ( tcdm_tx_add_o        ),
       .tcdm_req_o          ( tcdm_tx_req_o        ),
       .tcdm_gnt_i          ( tcdm_tx_gnt_i        ),
       
       .ext_sid_o           ( ext_tx_sid_o         ),
       .ext_opc_o           ( ext_tx_opc_o         ),
       .ext_len_o           ( ext_tx_len_o         ),
       .ext_bst_o           ( ext_tx_bst_o         ),
       .ext_add_o           ( ext_tx_add_o         ),
       .ext_req_o           ( ext_tx_req_o         ),
       .ext_gnt_i           ( ext_tx_gnt_i         ),
       
       .trans_tx_ext_add_o  ( trans_tx_ext_add_o   ),
       .trans_tx_tcdm_add_o ( trans_tx_tcdm_add_o  ),
       .trans_tx_len_o      ( trans_tx_len_o       ),
       .trans_tx_req_o      ( trans_tx_req_o       ),
       .trans_tx_gnt_i      ( trans_tx_gnt_i       )
       );
   
   trans_unpack
     #(
       .TRANS_SID_WIDTH     ( TRANS_SID_WIDTH     ),
       .TCDM_ADD_WIDTH      ( TCDM_ADD_WIDTH      ),
       .EXT_ADD_WIDTH       ( EXT_ADD_WIDTH       ),
       .MCHAN_BURST_LENGTH  ( MCHAN_BURST_LENGTH  )
       )
   rx_trans_unpack_i
     (
      .clk_i                ( clk_gated_o         ),
      .rst_ni               ( rst_ni              ),
      
      .mchan_sid_i          ( s_rx_queue_sid      ),
      .mchan_opc_i          ( s_rx_queue_opc      ),
      .mchan_len_i          ( s_rx_queue_len      ),
      .mchan_inc_i          ( s_rx_queue_inc      ),
      .mchan_tcdm_add_i     ( s_rx_queue_tcdm_add ),
      .mchan_ext_add_i      ( s_rx_queue_ext_add  ),
      .mchan_req_i          ( s_rx_queue_req      ),
      .mchan_gnt_o          ( s_rx_queue_gnt      ),
      
      .tcdm_sid_o           (                     ),
      .tcdm_opc_o           (                     ),
      .tcdm_len_o           (                     ),
      .tcdm_add_o           ( ext_rx_tcdm_add_o   ),
      .tcdm_req_o           (                     ),
      .tcdm_gnt_i           ( 1'b1                ),
      
      .ext_sid_o            ( ext_rx_sid_o        ),
      .ext_opc_o            ( ext_rx_opc_o        ),
      .ext_len_o            ( ext_rx_len_o        ),
      .ext_add_o            ( ext_rx_add_o        ),
      .ext_bst_o            ( ext_rx_bst_o        ),
      .ext_req_o            ( ext_rx_req_o        ),
      .ext_gnt_i            ( ext_rx_gnt_i        ),
      
      .trans_tx_ext_add_o   (                     ),
      .trans_tx_tcdm_add_o  (                     ),
      .trans_tx_len_o       (                     ),
      .trans_tx_req_o       (                     ),
      .trans_tx_gnt_i       ( 1'b1                )
      );
   
   //**********************************************************
   //*************** GENERATION OF BUSY SIGNAL ****************
   //**********************************************************
   
   assign busy_o = ( | s_cores_busy ) | ( | s_trans_alloc_status );
   
   //**********************************************************
   //*************** ARCHITECTURAL CLOCK GATING ***************
   //**********************************************************
   			
   cluster_clock_gating mchan_ckgate
     (
      .clk_i      ( clk_i        ),
      .en_i       ( busy_o       ),
      .test_en_i  ( test_mode_i  ),
      .clk_o      ( clk_gated_o  )
      );
   
endmodule
