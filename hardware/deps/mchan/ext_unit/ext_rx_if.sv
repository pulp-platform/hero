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

module ext_rx_if
  #(
    parameter AXI_ADDR_WIDTH  = 32,
    parameter AXI_DATA_WIDTH  = 64,
    parameter AXI_USER_WIDTH  = 6,
    parameter AXI_ID_WIDTH    = 4,
    parameter AXI_STRB_WIDTH  = AXI_DATA_WIDTH/8,
    parameter EXT_ADD_WIDTH   = 29,
    parameter EXT_OPC_WIDTH   = 12,
    parameter EXT_TID_WIDTH   = 4,
    parameter MCHAN_LEN_WIDTH = 15
    )
   (
    
    input  logic                      clk_i,
    input  logic                      rst_ni,
    
    // IN CMD INTERFACE
    //***************************************
    input  logic [EXT_ADD_WIDTH-1:0]  cmd_add_i,
    input  logic [EXT_OPC_WIDTH-1:0]  cmd_opc_i,
    input  logic [MCHAN_LEN_WIDTH-1:0]cmd_len_i,
    input  logic [EXT_TID_WIDTH-1:0]  cmd_tid_i,
    input  logic                      cmd_bst_i,
    input  logic                      cmd_req_i,
    output logic                      cmd_gnt_o,
    
    output logic                      tcdm_req_o,
    input  logic                      tcdm_gnt_i,
    
    output logic                      trans_rx_req_o,
    input  logic                      trans_rx_gnt_i,
    
    input  logic                      valid_tid_i,
    output logic                      release_tid_o,
    output logic [EXT_TID_WIDTH-1:0]  res_tid_o,
    
    output logic                      synch_req_o,
    
    // READ DATA INTERFACE
    //***************************************
    output logic [63:0]               rx_data_dat_o,
    output logic                      rx_data_req_o,
    input  logic                      rx_data_gnt_i,
    
    // AXI4 MASTER
    //***************************************
    
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
    
    // READ DATA CHANNEL
    input  logic                      axi_master_r_valid_i,
    input  logic [AXI_DATA_WIDTH-1:0] axi_master_r_data_i,
    input  logic [1:0]                axi_master_r_resp_i,
    input  logic                      axi_master_r_last_i,
    input  logic [AXI_ID_WIDTH-1:0]   axi_master_r_id_i,
    input  logic [AXI_USER_WIDTH-1:0] axi_master_r_user_i,
    output logic                      axi_master_r_ready_o
    
    );
   
   enum 			      `ifdef SYNTHESIS logic [1:0] `endif { TRANS_IDLE, TRANS_STALLED, TRANS_RUN } CS, NS;
   logic [AXI_ID_WIDTH+4-1:0]	      s_axi_master_ar_id;
   
   logic [7:0] 			      s_beats_nb,s_beats_nb_align;
   
   //COMPUTES NUMBER OF BEATS
   assign s_beats_nb = cmd_len_i >> 3;
   
   always_comb
     begin
        if ( cmd_add_i[2:0] + cmd_len_i[2:0] < 8 )
          s_beats_nb_align = s_beats_nb;
        else
          s_beats_nb_align = s_beats_nb + 1;
     end
   
   //**********************************************************
   //*************** REQUEST CONTROL CHANNEL ******************
   //**********************************************************
   
   always_comb
     begin
	
	if ( cmd_req_i             == 1'b1 && // THE CMD QUEUE CONTAINS A VALID COMMAND
	     axi_master_ar_ready_i == 1'b1 && // THE WRITE ADDRESS CHANNEL IS ABLE TO ACCETT A BEAT
	     valid_tid_i           == 1'b1 )  // THE TID GEN CONTAINS A VALID ID
	  begin
	     cmd_gnt_o             = 1'b1; // READ CMD FROM CMD QUEUE
	     axi_master_ar_valid_o = 1'b1; // ASSERT REQUEST SIGNAL ON AR CHANNEL
	  end
	else
	  begin
	     cmd_gnt_o             = 1'b0;
	     axi_master_ar_valid_o = 1'b0;
	  end
	
     end
   
   //**********************************************************
   //*************** RESPONSE CONTROL CHANNEL *****************
   //**********************************************************
   
   // UPDATES THE STATE
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  CS <= TRANS_IDLE;
	else
	  CS <= NS;
     end
   
   // COMPUTES NEXT STATE
   always_comb
     begin
	
	tcdm_req_o     = 1'b0;
	trans_rx_req_o = 1'b0;
	
	case(CS)
	  
	  TRANS_IDLE:
	    begin
	       if ( trans_rx_gnt_i       == 1'b1 &&
		    tcdm_gnt_i           == 1'b1 &&
		    rx_data_gnt_i        == 1'b1 &&
		    axi_master_r_valid_i == 1'b1 && // TRANSACTION STARTS WHEN R_VALID ON DATA CHANNEL IS DETECTED
		    axi_master_r_last_i  == 1'b0 )  // BURST
		 begin
		    tcdm_req_o     = 1'b1;
		    trans_rx_req_o = 1'b1;
		    NS             = TRANS_RUN;
		 end
	       else
		 if ( trans_rx_gnt_i       == 1'b1 &&
		      tcdm_gnt_i           == 1'b1 &&
		      rx_data_gnt_i        == 1'b1 &&
		      axi_master_r_valid_i == 1'b1 && // TRANSACTION STARTS WHEN R_VALID ON DATA CHANNEL IS DETECTED
		      axi_master_r_last_i  == 1'b1 )  // SIGNLE BEAT
		   begin
		      tcdm_req_o     = 1'b1;
		      trans_rx_req_o = 1'b1;
		      NS             = TRANS_IDLE;
		   end
		 else
		   begin
		      NS = TRANS_IDLE;
		   end
	    end
	  
	  TRANS_RUN:
	    begin
	       if ( rx_data_gnt_i        == 1'b1 && // TRANSACTION FINISHES WHAN LAST BEAT ON DATA CHANNEL IS DETECTED
		    axi_master_r_last_i  == 1'b1 &&
		    axi_master_r_valid_i == 1'b1 ) // RUNNING
		 NS = TRANS_IDLE;
	       else
		 NS = TRANS_RUN;
	    end
	  
	  default:
	    NS = TRANS_IDLE;
	  
	endcase
	
     end
   
   //**********************************************************
   //*************** RESPONSE DATA CHANNEL ********************
   //**********************************************************
   
   always_comb
     begin
	if ( axi_master_r_valid_i == 1'b1 &&
	     rx_data_gnt_i        == 1'b1 )
	  begin
	     if ( axi_master_r_last_i == 1'b1 )
	       begin
		  axi_master_r_ready_o = 1'b1;
		  rx_data_req_o        = 1'b1;
		  release_tid_o        = 1'b1;
		  synch_req_o          = 1'b1;
	       end
	     else
	       begin
		  axi_master_r_ready_o = 1'b1;
		  rx_data_req_o        = 1'b1;
		  release_tid_o        = 1'b0;
		  synch_req_o          = 1'b0;
	       end
	  end
	else
	  begin
	     axi_master_r_ready_o = 1'b0;
	     rx_data_req_o        = 1'b0;
	     release_tid_o        = 1'b0;
	     synch_req_o          = 1'b0;
	  end
     end
   
   //**********************************************************
   //********** BINDING OF INPUT/OUTPUT SIGNALS ***************
   //**********************************************************
   
   assign axi_master_ar_addr_o   = cmd_add_i;
   assign axi_master_ar_prot_o   = '0;
   assign axi_master_ar_region_o = '0;
   assign axi_master_ar_len_o    = s_beats_nb_align;
   assign axi_master_ar_size_o   = 3'd3;
   assign axi_master_ar_burst_o  = {1'b0,cmd_bst_i};
   assign axi_master_ar_lock_o   = '0;
   assign axi_master_ar_cache_o  = '0;
   assign axi_master_ar_qos_o    = '0;
   assign axi_master_ar_user_o   = '0;
   
   assign s_axi_master_ar_id     = {{(AXI_ID_WIDTH+4-EXT_TID_WIDTH){1'b0}},cmd_tid_i};
   assign axi_master_ar_id_o     = s_axi_master_ar_id[AXI_ID_WIDTH-1:0];
   
   assign rx_data_dat_o          = axi_master_r_data_i;
   assign res_tid_o              = axi_master_r_id_i[EXT_TID_WIDTH-1:0];
   
endmodule
