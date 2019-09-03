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

module mchan_address_decoder
  #(
    // OVERRRIDDEN FROM TOP
    parameter TCDM_ADD_WIDTH      = 12,
    parameter EXT_ADD_WIDTH       = 29,
    parameter NB_TRANSFERS        = 4,
    parameter TWD_COUNT_WIDTH     = 16,
    parameter TWD_STRIDE_WIDTH    = 16,
    parameter TWD_QUEUE_DEPTH     = 4,
    // DEFINED IN MCHAN_DEFINES
    parameter TWD_QUEUE_ADD_WIDTH = $clog2(TWD_QUEUE_DEPTH),
    parameter TRANS_SID_WIDTH     = $clog2(NB_TRANSFERS),
    parameter MCHAN_OPC_WIDTH     = `MCHAN_OPC_WIDTH,
    parameter MCHAN_LEN_WIDTH     = `MCHAN_LEN_WIDTH
    )
   (
    
    input  logic                           clk_i,
    input  logic                           rst_ni,
    
    // CONTROL TARGET
    //***************************************
    input  logic                           ctrl_targ_req_i,
    input  logic                           ctrl_targ_type_i,
    input  logic [3:0]                     ctrl_targ_be_i,
    input  logic [31:0]                    ctrl_targ_add_i,
    input  logic [31:0]                    ctrl_targ_data_i,
    output logic                           ctrl_targ_gnt_o,
    
    output logic                           ctrl_targ_r_valid_o,
    output logic [31:0]                    ctrl_targ_r_data_o,
    
    // CMD FIFO INTERFACE
    //***************************************
    input  logic                           cmd_gnt_i,
    output logic                           cmd_req_o,
    output logic [MCHAN_LEN_WIDTH-1:0]     cmd_len_o,
    output logic [MCHAN_OPC_WIDTH-1:0]     cmd_opc_o,
    output logic                           cmd_inc_o,
    output logic                           cmd_twd_o,
    output logic                           cmd_ele_o,
    output logic                           cmd_ile_o,
    output logic                           cmd_ble_o,
    output logic [TWD_QUEUE_ADD_WIDTH-1:0] cmd_twd_add_o,
    output logic [TRANS_SID_WIDTH-1:0]     cmd_sid_o,
    
    // TCDM FIFO INTERFACE
    //***************************************
    input  logic                           tcdm_gnt_i,
    output logic                           tcdm_req_o,
    output logic [TCDM_ADD_WIDTH-1:0]      tcdm_add_o,
    
    // EXT FIFO INTERFACE
    //***************************************
    input  logic                           ext_gnt_i,
    output logic                           ext_req_o,
    output logic [EXT_ADD_WIDTH-1:0]       ext_add_o,
    
    // SYNCH UNIT INTERFACE
    //***************************************
    input  logic                           arb_gnt_i,
    input  logic                           arb_req_i,
    input  logic [TRANS_SID_WIDTH-1:0]     arb_sid_i,
    
    // TWD FIFO INTERFACE
    //***************************************
    output logic                           twd_trans_o,
    
    output logic                           twd_alloc_req_o,
    input  logic                           twd_alloc_gnt_i,
    input  logic [TWD_QUEUE_ADD_WIDTH-1:0] twd_alloc_add_i,
    
    output logic                           twd_queue_req_o,
    output logic [TWD_QUEUE_ADD_WIDTH-1:0] twd_queue_add_o,
    output logic [TWD_COUNT_WIDTH-1:0]     twd_queue_count_o,
    output logic [TWD_STRIDE_WIDTH-1:0]    twd_queue_stride_o,
    output logic [TRANS_SID_WIDTH-1:0]     twd_queue_sid_o,
    
    // TRANSFER BUFFER INTERFACE
    //***************************************
    // RETRIVE SID SIGNALS
    output logic                           trans_alloc_req_o,
    input  logic                           trans_alloc_gnt_i,
    input  logic [TRANS_SID_WIDTH-1:0]     trans_alloc_ret_i,
    // CLEAR SID SIGNALS
    output logic [NB_TRANSFERS-1:0]        trans_alloc_clr_o,
    // ALLOC STATUS SIGNALS
    input  logic [NB_TRANSFERS-1:0]        trans_alloc_status_i,
    
    // TRANSFERS STATUS
    input  logic [NB_TRANSFERS-1:0]        trans_status_i,
    
    output logic                           busy_o
    
    );
   
   enum 				   `ifdef SYNTHESIS logic [3:0] `endif { IDLE, STATUS_GRANTED, RET_ID_GRANTED, CLR_ID_GRANTED, CMD, CMD_GRANTED, TCDM, TCDM_GRANTED, EXT, EXT_GRANTED, TWD, TWD_GRANTED, TWD_GRANTED_NOWAIT, BUSY, BUSY2 } CS, NS;
   
   logic 				   s_twd_trans;
   logic [TWD_QUEUE_ADD_WIDTH-1:0] 	   s_twd_add;
   logic [TRANS_SID_WIDTH-1:0] 		   s_trans_sid;
   
   //**********************************************************
   //*************** ADDRESS DECODER **************************
   //**********************************************************
   
   // UPDATE THE STATE
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     CS              <= IDLE;
	  end
	else
	  begin
	     CS              <= NS;
	  end
     end
   
   //COMPUTE NEXT STATE
   always_comb
     begin
	
	ctrl_targ_r_valid_o = 1'b0;
	ctrl_targ_r_data_o  = '0;
	ctrl_targ_gnt_o     = 1'b0;
	trans_alloc_req_o   = 1'b0;
	trans_alloc_clr_o   = 1'b0;
	cmd_req_o           = 1'b0;
	tcdm_req_o          = 1'b0;
	ext_req_o           = 1'b0;
	twd_alloc_req_o     = 1'b0;
	twd_queue_req_o     = 1'b0;
	busy_o              = 1'b1;
	
	case(CS)
	  
	  IDLE:
	    begin
	       busy_o = 1'b0;
	       if ( ctrl_targ_req_i == 1'b1 )
		 begin
		    busy_o = 1'b1;
		    case(ctrl_targ_add_i[3:0])
		      
		      `MCHAN_CMD_ADDR:
			begin
			   if ( ctrl_targ_type_i == 1'b1 ) // READ OPERATION: RETRIVE ID --> REQUIRES ARBITRATION
			     begin
				trans_alloc_req_o = 1'b1;
				if ( trans_alloc_gnt_i == 1'b1 ) // RETRIVE ID GRANTED
				  begin
				     ctrl_targ_gnt_o = 1'b1;
				     NS = RET_ID_GRANTED;
				  end
				else // RETRIVE ID STALLED
				  begin
				     ctrl_targ_gnt_o = 1'b0;
				     NS = IDLE;
				  end
			     end
			   else // WRITE OPERATION: ENQUEUE COMMAND
			     begin
				if ( cmd_gnt_i == 1'b1 ) // CMD FIFO NOT FULL
				  begin
				     if ( cmd_twd_o == 1'b1 )
				       begin
					  twd_alloc_req_o = 1'b1;
					  if ( twd_alloc_gnt_i == 1'b1 ) // THE TWD CMD FIFO IS NOT FULL
					    begin
					       ctrl_targ_gnt_o = 1'b1;
					       cmd_req_o       = 1'b1;
					       NS              = CMD_GRANTED;
					    end
					  else // THE TWD CMD FIFO IS FULL: STALL
					    begin
					       ctrl_targ_gnt_o = 1'b0;
					       cmd_req_o       = 1'b0;
					       NS              = IDLE;
					    end
				       end
				     else // NOT A 2D TRANSFER
				       begin
					  NS              = CMD_GRANTED;
					  ctrl_targ_gnt_o = 1'b1;
					  cmd_req_o       = 1'b1;
				       end
				  end
				else // CMD FIFO FULL: STALL
				  begin
				     ctrl_targ_gnt_o = 1'b0;
				     cmd_req_o       = 1'b0;
				     NS              = IDLE;
				  end 
			     end
			end
		      
		      `MCHAN_STATUS_ADDR:
			begin
			   if ( ctrl_targ_type_i == 1'b1 ) // READ OPERATION: RETRIVE STATUS --> ALWAYS GRANTED
			     begin
				ctrl_targ_gnt_o = 1'b1;
				NS              = STATUS_GRANTED;
			     end
			   else // WRITE OPERATION: CLEAR TRANSFER --> ALWAYS GRANTED
			     begin
				ctrl_targ_gnt_o   = 1'b1;
				trans_alloc_clr_o = ctrl_targ_data_i[NB_TRANSFERS-1:0];
				NS                = CLR_ID_GRANTED;
			     end
			end
		      
		      default:
			begin
			   NS = IDLE;
			end
		      
		    endcase
		    
		 end
	       
	       else
		 
		 begin
		    NS = IDLE;
		 end
	       
	    end
	  
	  STATUS_GRANTED:
	    begin
	       ctrl_targ_r_data_o[NB_TRANSFERS-1:0]     = trans_status_i;
	       ctrl_targ_r_data_o[16+NB_TRANSFERS-1:16] = trans_alloc_status_i;
	       ctrl_targ_r_valid_o                      = 1'b1;
	       ctrl_targ_gnt_o                          = 1'b0;
	       NS                                       = IDLE;
	    end
	  
	  CLR_ID_GRANTED:
	    begin
	       ctrl_targ_r_valid_o = 1'b1;
	       ctrl_targ_gnt_o     = 1'b0;
	       NS                  = IDLE;
	    end
	  
	  RET_ID_GRANTED:
	    begin
	       ctrl_targ_r_data_o  = {{(32-TRANS_SID_WIDTH){1'b0}} , s_trans_sid};
	       ctrl_targ_r_valid_o = 1'b1;
	       if ( ctrl_targ_req_i == 1'b1 && cmd_gnt_i == 1'b1 ) // CMD FIFO NOT FULL
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 if ( cmd_twd_o == 1'b1 )
			   begin
			      twd_alloc_req_o = 1'b1;
			      if ( twd_alloc_gnt_i == 1'b1 ) // THE TWD CMD FIFO IS NOT FULL
				begin
				   ctrl_targ_gnt_o = 1'b1;
				   NS              = CMD_GRANTED;
				   cmd_req_o       = 1'b1;
				end
			      else
				begin
				   NS              = CMD;
				   cmd_req_o       = 1'b0;
				end
			   end
			 else
			   begin
			      NS              = CMD_GRANTED;
			      ctrl_targ_gnt_o = 1'b1;
			      cmd_req_o       = 1'b1;
			   end
		      end
		    else // WRONG ADDRESS/POLARITY
		      begin
			 NS = IDLE;  // ERROR
		      end
		 end
	       else
		 begin
		    NS = CMD;
		 end
	    end
	  
	  CMD:
	    begin
	       if ( ctrl_targ_req_i == 1'b1 && cmd_gnt_i == 1'b1 ) // CMD FIFO NOT FULL
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 if ( cmd_twd_o == 1'b1 )
			   begin
			      twd_alloc_req_o = 1'b1;
			      if ( twd_alloc_gnt_i == 1'b1 ) // THE TWD CMD FIFO IS NOT FULL
				begin
				   ctrl_targ_gnt_o = 1'b1;
				   NS              = CMD_GRANTED;
				   cmd_req_o       = 1'b1;
				end
			      else
				begin
				   NS              = CMD;
				end
			   end
			 else // NOT TWOD
			   begin
			      cmd_req_o       = 1'b1;
			      ctrl_targ_gnt_o = 1'b1;
			      NS              = CMD_GRANTED;
			   end
		      end
		    else // WRONG ADDRESS/POLARITY
		      begin
			 NS = IDLE;  // ERROR
		      end
		 end
	       else
		 begin
		    NS              = CMD;
		 end
	    end
	  
	  CMD_GRANTED:
	    begin
	       ctrl_targ_r_valid_o = 1'b1;
	       if ( ctrl_targ_req_i == 1'b1 & tcdm_gnt_i == 1'b1 ) // TCDM ADDR FIFO NOT FULL
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 NS              = TCDM_GRANTED;
			 ctrl_targ_gnt_o = 1'b1;
			 tcdm_req_o      = 1'b1;
		      end
		    else // WRONG ADDRESS/POLARITY
		      begin
			 NS = IDLE; // ERROR
		      end
		 end
	       else
		 begin
		    NS = TCDM;
		 end
	    end
	  
	  TCDM:
	    begin
	       if ( ctrl_targ_req_i == 1'b1 & tcdm_gnt_i == 1'b1 ) // TCDM ADDR FIFO NOT FULL
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 NS              = TCDM_GRANTED;
			 ctrl_targ_gnt_o = 1'b1;
			 tcdm_req_o      = 1'b1;
		      end
		    else // WRONG ADDRESS/POLARITY
		      begin
			 NS = IDLE; // ERROR
		      end
		 end
	       else
		 begin
		    NS              = TCDM;
		 end
	    end
	  
	  TCDM_GRANTED:
	    begin
	       ctrl_targ_r_valid_o = 1'b1;
	       if ( ctrl_targ_req_i == 1'b1 & ext_gnt_i == 1'b1 ) // EXT ADDR FIFO NOT FULL
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 NS              = EXT_GRANTED;
			 ctrl_targ_gnt_o = 1'b1;
			 ext_req_o       = 1'b1;
		      end
		    else // WRONG ADDRESS/POLARITY
		      begin
			 NS = IDLE; // ERROR
		      end
		 end
	       else
		 begin
		    NS = EXT;
		 end
	    end
	  
	  EXT:
	    begin
	       if ( ctrl_targ_req_i == 1'b1 & ext_gnt_i == 1'b1 ) // EXT ADDR FIFO NOT FULL
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 NS              = EXT_GRANTED;
			 ctrl_targ_gnt_o = 1'b1;
			 ext_req_o       = 1'b1;
		      end
		    else // WRONG ADDRESS/POLARITY
		      begin
			 NS = IDLE; // ERROR
		      end
		 end
	       else
		 begin
		    NS = EXT;
		 end
	    end
	  
	  EXT_GRANTED:
	    begin
	       ctrl_targ_r_valid_o = 1'b1;
	       if ( ctrl_targ_req_i == 1'b1 )
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 if ( s_twd_trans == 1'b1 ) // IT'S A TWD TRANSFER
			   begin
			      twd_queue_req_o = 1'b1;
			      ctrl_targ_gnt_o = 1'b1;
			      if( ( arb_req_i == 1'b1 ) && ( arb_gnt_i == 1'b1 ) && ( arb_sid_i == s_trans_sid ) )
				NS                  = TWD_GRANTED_NOWAIT;
			      else
				NS                  = TWD_GRANTED;
			   end
			 else // NOT A TWD TRANSFER
			   begin
			      if( ( arb_req_i == 1'b1 ) && ( arb_gnt_i == 1'b1 ) && ( arb_sid_i == s_trans_sid ) )
				NS                  = BUSY2;
			      else
				NS                  = BUSY;
			   end
		      end
		    else
		      begin
			 if( ( arb_req_i == 1'b1 ) && ( arb_gnt_i == 1'b1 ) && ( arb_sid_i == s_trans_sid ) )
			   NS                  = BUSY2;
			 else
			   NS                  = BUSY;
		      end
		 end
	       else // NOT A REQUEST
		 begin
		    if ( s_twd_trans == 1'b1 ) // IT'S A TWD TRANSFER
		      begin
			 NS = TWD;
		      end
		    else
		      begin
			 if( ( arb_req_i == 1'b1 ) && ( arb_gnt_i == 1'b1 ) && ( arb_sid_i == s_trans_sid ) )
			   NS                  = BUSY2;
			 else
			   NS                  = BUSY;
		      end
		 end
	    end
	  
	  TWD:
	    begin
	       if ( ctrl_targ_req_i == 1'b1 ) // TWD ADDR FIFO NOT FULL
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 ctrl_targ_gnt_o = 1'b1;
			 twd_queue_req_o = 1'b1;
			 if( ( arb_req_i == 1'b1 ) && ( arb_gnt_i == 1'b1 ) && ( arb_sid_i == s_trans_sid ) )
			   NS                  = TWD_GRANTED_NOWAIT;
			 else
			   NS                  = TWD_GRANTED;
		      end
		    else
		      begin // WRONG ADDRESS/POLARITY
			 NS = IDLE; // ERROR
		      end
		 end
	       else
		 begin
		    NS              = TWD;
		 end
	    end
	  
	  TWD_GRANTED:
	    begin
	       ctrl_targ_r_valid_o = 1'b1;
	       begin
	       	  if( ( arb_req_i == 1'b1 ) && ( arb_gnt_i == 1'b1 ) && ( arb_sid_i == s_trans_sid ) )
		    NS                  = BUSY2;
		  else
		    NS                  = BUSY;
	       end
	    end
	  
	  TWD_GRANTED_NOWAIT:
	    begin
	       ctrl_targ_r_valid_o = 1'b1;
	       NS                  = BUSY2;
	    end
	  
	  BUSY:
	    begin
	       if( ( arb_req_i == 1'b1 ) && ( arb_gnt_i == 1'b1 ) && ( arb_sid_i == s_trans_sid ) )
		 NS                  = BUSY2;
	       else
		 NS                  = BUSY;
	    end
	  
	  BUSY2:
	    begin
	       if( trans_status_i[s_trans_sid] == 1'b1 )
		 NS                  = IDLE;
	       else
		 NS                  = BUSY2;
	    end
	  
	  default:
	    begin
	       NS                  = IDLE;
	    end
	  
	endcase
	
     end
   
   // REGISTER TO STORE SID
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     s_trans_sid <= 1'b0;
	  end
	else
	  begin
	     if(trans_alloc_req_o == 1'b1 && trans_alloc_gnt_i == 1'b1)
	       begin
		  s_trans_sid <= trans_alloc_ret_i;
	       end
	  end
     end
   
   // REGISTER TO STORE TWD ADDRESS
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     s_twd_add <= 1'b0;
	  end
	else
	  begin
	     if(twd_alloc_req_o == 1'b1 && twd_alloc_gnt_i == 1'b1)
	       begin
		  s_twd_add <= twd_alloc_add_i;
	       end
	  end
     end
   
   // REGISTER TO INTERNALLY STORE TWD TRANSFER STATUS BIT
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     s_twd_trans <= 1'b0;
	  end
	else
	  begin
	     if (cmd_req_o == 1'b1 && cmd_gnt_i == 1'b1 && ctrl_targ_data_i[MCHAN_LEN_WIDTH+3] == 1'b1)
	       begin
		  s_twd_trans <= 1'b1;
	       end
	     else
	       begin
		  if (twd_queue_req_o == 1'b1)
		    begin
		       s_twd_trans <= 1'b0;
		    end
	       end
	  end
     end
   
   assign cmd_len_o          = ctrl_targ_data_i[MCHAN_LEN_WIDTH:0]-1;                 // TRANSFER LENGTH
   assign cmd_opc_o          = ctrl_targ_data_i[MCHAN_LEN_WIDTH+1:MCHAN_LEN_WIDTH+1]; // TRANSFER OPCODE
   assign cmd_inc_o          = ctrl_targ_data_i[MCHAN_LEN_WIDTH+2:MCHAN_LEN_WIDTH+2]; // INCREMENTAL TRANSFER
   assign cmd_twd_o          = ctrl_targ_data_i[MCHAN_LEN_WIDTH+3:MCHAN_LEN_WIDTH+3]; // 2D TRANSFER
   assign cmd_ele_o          = ctrl_targ_data_i[MCHAN_LEN_WIDTH+4:MCHAN_LEN_WIDTH+4]; // EVENT LINES ENABLE
   assign cmd_ile_o          = ctrl_targ_data_i[MCHAN_LEN_WIDTH+5:MCHAN_LEN_WIDTH+5]; // INTERRUPT LINES ENABLE
   assign cmd_ble_o          = ctrl_targ_data_i[MCHAN_LEN_WIDTH+6:MCHAN_LEN_WIDTH+6]; // BROADCAST LINES ENABLE
   assign cmd_sid_o          = s_trans_sid;
   assign cmd_twd_add_o      = twd_alloc_add_i;
   assign tcdm_add_o         = ctrl_targ_data_i[TCDM_ADD_WIDTH-1:0];
   assign ext_add_o          = ctrl_targ_data_i[EXT_ADD_WIDTH-1:0];
   assign twd_queue_count_o  = ctrl_targ_data_i[TWD_COUNT_WIDTH:0]-1;
   assign twd_queue_stride_o = ctrl_targ_data_i[15+TWD_STRIDE_WIDTH:16]-1;
   assign twd_queue_add_o    = s_twd_add;
   assign twd_queue_sid_o    = s_trans_sid;
   assign twd_trans_o        = s_twd_trans;
   
endmodule
