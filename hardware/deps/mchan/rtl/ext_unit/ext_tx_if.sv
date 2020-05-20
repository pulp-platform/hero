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

module ext_tx_if
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
    input  logic [EXT_ADD_WIDTH-1:0]   cmd_add_i,
    input  logic [EXT_OPC_WIDTH-1:0]   cmd_opc_i,
    input  logic [MCHAN_LEN_WIDTH-1:0] cmd_len_i,
    input  logic [EXT_TID_WIDTH-1:0]   cmd_tid_i,
    input  logic                       cmd_bst_i,
    input  logic                       cmd_req_i,
    output logic                       cmd_gnt_o,
    
    input  logic                       valid_tid_i,
    
    output logic                       release_tid_o,
    output logic [EXT_TID_WIDTH-1:0]   res_tid_o,
    
    output logic                       synch_req_o,
    
    // WRITE DATA INTERFACE
    //***************************************
    input  logic [63:0]                tx_data_dat_i,
    input  logic [7:0]                 tx_data_strb_i,
    output logic                       tx_data_req_o,
    input  logic                       tx_data_gnt_i,
    
    // AXI4 MASTER
    //***************************************
    // WRITE ADDRESS CHANNEL
    output logic                       axi_master_aw_valid_o,
    output logic [AXI_ADDR_WIDTH-1:0]  axi_master_aw_addr_o,
    output logic [2:0]                 axi_master_aw_prot_o,
    output logic [3:0]                 axi_master_aw_region_o,
    output logic [7:0]                 axi_master_aw_len_o,
    output logic [2:0]                 axi_master_aw_size_o,
    output logic [1:0]                 axi_master_aw_burst_o,
    output logic                       axi_master_aw_lock_o,
    output logic [3:0]                 axi_master_aw_cache_o,
    output logic [3:0]                 axi_master_aw_qos_o,
    output logic [AXI_ID_WIDTH-1:0]    axi_master_aw_id_o,
    output logic [AXI_USER_WIDTH-1:0]  axi_master_aw_user_o,
    input  logic                       axi_master_aw_ready_i,
    
    // WRITE DATA CHANNEL
    output logic                       axi_master_w_valid_o,
    output logic [AXI_DATA_WIDTH-1:0]  axi_master_w_data_o,
    output logic [AXI_STRB_WIDTH-1:0]  axi_master_w_strb_o,
    output logic [AXI_USER_WIDTH-1:0]  axi_master_w_user_o,
    output logic                       axi_master_w_last_o,
    input  logic                       axi_master_w_ready_i,
    
    // WRITE RESPONSE CHANNEL
    input  logic                       axi_master_b_valid_i,
    input  logic [1:0]                 axi_master_b_resp_i,
    input  logic [AXI_ID_WIDTH-1:0]    axi_master_b_id_i,
    input  logic [AXI_USER_WIDTH-1:0]  axi_master_b_user_i,
    output logic                       axi_master_b_ready_o
    
    );
   
   // FSM STATES SIGNALS
   enum 			      `ifdef TARGET_SYNTHESIS logic [1:0] `endif { TRANS_IDLE, TRANS_ACK, TRANS_RUN } CS, NS;
   
   logic [7:0] 			      s_beats_nb,
                                      s_beats_nb_align,
				      s_beats_nb_reg,
				      s_beats_count;
   logic 			      s_trans_complete,
				      s_start_count;
   logic [AXI_ID_WIDTH+4-1:0] 	      s_axi_master_aw_id;
   
   //COMPUTE NUMBER OF BEATS
   assign s_beats_nb = cmd_len_i >> 3;
   
   always_comb
     begin
        if ( cmd_add_i[2:0] + cmd_len_i[2:0] < 8 )
          s_beats_nb_align = s_beats_nb;
        else
          s_beats_nb_align = s_beats_nb + 1;
     end
   
   //SAMPLES THE OPCODE AND THE ADDRESS
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
	if (rst_ni == 1'b0)
	  begin
	     s_beats_nb_reg <= '0;
	  end
	else
	  begin
	     if ( cmd_req_i == 1'b1 &&
		  cmd_gnt_o == 1'b1 &&
		  valid_tid_i == 1'b1 )
	       begin
		  s_beats_nb_reg <= s_beats_nb_align;
	       end
	  end
     end
   
   //COUNTER FOR NUMBER OF BEATS
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  s_beats_count <= 8'b0;
	else
	  if ( s_start_count == 1'b1 )
	    s_beats_count <= 8'b0;
	  else
	    if ( tx_data_req_o        == 1'b1 &&
                 tx_data_gnt_i        == 1'b1 &&
                 axi_master_w_ready_i == 1'b1 &&
                 axi_master_w_valid_o == 1'b1 )
	      s_beats_count <= s_beats_count+1;
	    else
	      s_beats_count <= s_beats_count;
     end
   
   always_comb
     begin
	if ( s_beats_count == s_beats_nb_reg-1 )
	  s_trans_complete = 1'b1;
	else
	  s_trans_complete = 1'b0;
     end
   
   //**********************************************************
   //*************** REQUEST CONTROL AND DATA CHANNEL ********* // MAYBE TO DECOUPLE CONTROL/DATA TO IMPROVE PERFORMANCE
   //**********************************************************
   
   // UPDATE THE STATE
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     CS <= TRANS_IDLE;
	  end
	else
	  begin
	     CS <= NS;
	  end
     end
   
   // COMPUTE NEXT STATE
   always_comb
     begin
	
	tx_data_req_o         = 1'b0;
        cmd_gnt_o             = 1'b0;
	axi_master_aw_valid_o = 1'b0;
	axi_master_w_valid_o  = 1'b0;
	axi_master_w_last_o   = 1'b0;
	
	s_start_count         = 1'b0;
	
	NS                    = TRANS_IDLE;
	
	case(CS)
	  
	  TRANS_IDLE:
	    begin
	       if ( cmd_req_i             == 1'b1 && // THE CMD QUEUE CONTAINS A VALID COMMAND
		    axi_master_aw_ready_i == 1'b1 && // THE WRITE ADDRESS CHANNEL IS ABLE TO ACCEPT A BEAT
		    valid_tid_i           == 1'b1 )  // THE TID GEN CONTAINS A VALID ID
		 begin
		    cmd_gnt_o             = 1'b1; // READ CMD FROM CMD QUEUE
		    axi_master_aw_valid_o = 1'b1; // ASSERT REQUEST SIGNAL ON AW CHANNEL
		    
		    if ( tx_data_gnt_i         == 1'b1 && // THE WRITE_BUFFER CONTAINS A BEAT
			 axi_master_w_ready_i  == 1'b1 )  // THE WRITE DATA CHANNEL IS ABLE TO ACCEPT A BEAT
		      begin
			 tx_data_req_o         = 1'b1; // READ DATA FROM THE FIFO
			 axi_master_w_valid_o  = 1'b1; // ASSERT REQUEST SIGNAL ON W CHANNEL
			 
			 if ( s_beats_nb_align == 8'd0 ) // SINGLE BEAT TRANSACTION
			   begin
			      axi_master_w_last_o = 1'b1;
			      NS                  = TRANS_IDLE;
			   end
			 else
			   begin //BURST
			      s_start_count = 1'b1;
			      NS = TRANS_RUN;
			   end
		      end
		    else
		      begin // AW CHANNEL OK, W CHANNEL NOT STARTED YET
			 s_start_count = 1'b0;
			 NS = TRANS_ACK;
		      end
		 end
	       else
		 begin
		    NS = TRANS_IDLE;
		 end
	    end
	  
	  TRANS_ACK:
	    begin
	       if ( tx_data_gnt_i        == 1'b1 &&  // THE WRITE_BUFFER CONTAINS A BEAT
		    axi_master_w_ready_i == 1'b1 )   // WCHANNEL IS ABLE TO ACCEPT A BEAT
		 begin
		    tx_data_req_o         = 1'b1; // READ DATA FROM THE FIFO
		    axi_master_w_valid_o  = 1'b1; // ASSERT REQUEST SIGNAL ON W CHANNEL
		    if ( s_beats_nb_reg == 8'd0 ) // SINGLE BEAT TRANSACTION
		      begin
			 axi_master_w_last_o = 1'b1;
			 NS                  = TRANS_IDLE;
		      end
		    else
		      begin //BURST
			 s_start_count = 1'b1;
			 NS = TRANS_RUN;
		      end
		 end
	       else
		 begin
		    NS = TRANS_ACK;
		 end
	    end
	  
	  TRANS_RUN:
	    begin
	       if ( tx_data_gnt_i        == 1'b1 &&  // THE WRITE_BUFFER CONTAINS A BEAT
		    axi_master_w_ready_i == 1'b1 )   // WCHANNEL IS ABLE TO ACCEPT A BEAT
		 begin
		    tx_data_req_o         = 1'b1; // READ DATA FROM THE FIFO
		    axi_master_w_valid_o  = 1'b1; // ASSERT REQUEST SIGNAL ON W CHANNEL
	       	    
		    if ( s_trans_complete      == 1'b1 && // TRANSACTION COMPLETE
			 axi_master_w_ready_i  == 1'b1 )  // THE WRITE DATA CHANNEL IS ABLE TO ACCEPT A BEAT
		      begin
			 axi_master_w_last_o = 1'b1;
			 NS = TRANS_IDLE;
		      end
		    else
		      begin
			 NS = TRANS_RUN;
		      end
		 end
	       else
		 begin
		    NS = TRANS_RUN;
		 end
	    end
	  
	  default:
	    begin
	       NS = TRANS_IDLE;
	    end
	  
	endcase
     end
   
   //**********************************************************
   //********** BINDING OF INPUT/OUTPUT SIGNALS ***************
   //**********************************************************
   
   assign axi_master_aw_addr_o   = cmd_add_i;
   assign axi_master_aw_prot_o   = '0;
   assign axi_master_aw_region_o = '0;
   assign axi_master_aw_len_o    = s_beats_nb_align;
   assign axi_master_aw_size_o   = 3'd3;
   assign axi_master_aw_burst_o  = {1'b0,cmd_bst_i};
   assign axi_master_aw_lock_o   = '0;
   assign axi_master_aw_cache_o  = 4'b0010; // modifiable
   assign axi_master_aw_qos_o    = '0;
   assign axi_master_aw_user_o   = '0;
   
   assign s_axi_master_aw_id     = { {(AXI_ID_WIDTH+4-EXT_TID_WIDTH){1'b0}}  ,cmd_tid_i};
   assign axi_master_aw_id_o     = s_axi_master_aw_id[AXI_ID_WIDTH-1:0];
   
   assign axi_master_w_data_o    = tx_data_dat_i;
   assign axi_master_w_strb_o    = tx_data_strb_i;
   assign axi_master_w_user_o    = '0;
   
   assign axi_master_b_ready_o   = 1'b1;
   
   assign release_tid_o = axi_master_b_valid_i;
   assign res_tid_o     = axi_master_b_id_i[EXT_TID_WIDTH-1:0];
   
   assign synch_req_o   = release_tid_o;
   
endmodule
