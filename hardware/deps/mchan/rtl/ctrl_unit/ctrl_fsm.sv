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

module ctrl_fsm
  #(
    // OVERRRIDDEN FROM TOP
    parameter TCDM_ADD_WIDTH      = 12,
    parameter EXT_ADD_WIDTH       = 29,
    parameter NB_TRANSFERS        = 4,
    parameter TWD_COUNT_WIDTH     = 16,
    parameter TWD_STRIDE_WIDTH    = 16,
    parameter TWD_QUEUE_DEPTH     = 4,
    parameter PE_ID_WIDTH         = 1,
    // DEFINED IN MCHAN_DEFINES
    parameter TWD_QUEUE_ADD_WIDTH = (TWD_QUEUE_DEPTH == 1) ? 1 : $clog2(TWD_QUEUE_DEPTH),
    parameter TRANS_SID_WIDTH     = (NB_TRANSFERS == 1) ? 1 : $clog2(NB_TRANSFERS),
    parameter MCHAN_OPC_WIDTH     = `MCHAN_OPC_WIDTH,
    parameter MCHAN_LEN_WIDTH     = `MCHAN_LEN_WIDTH
    )
   (
    
    input logic 			   clk_i,
    input logic 			   rst_ni,
    
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
    
    // CMD FIFO INTERFACE
    //***************************************
    input logic 			   cmd_gnt_i,
    output logic 			   cmd_req_o,
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
    
    // TCDM FIFO INTERFACE
    //***************************************
    input logic 			   tcdm_gnt_i,
    output logic 			   tcdm_req_o,
    output logic [TCDM_ADD_WIDTH-1:0] 	   tcdm_add_o,
    
    // EXT FIFO INTERFACE
    //***************************************
    input logic 			   ext_gnt_i,
    output logic 			   ext_req_o,
    output logic [EXT_ADD_WIDTH-1:0] 	   ext_add_o,
    
    // SYNCH UNIT INTERFACE
    //***************************************
    input logic 			   arb_gnt_i,
    input logic 			   arb_req_i,
    input logic [TRANS_SID_WIDTH-1:0] 	   arb_sid_i,
    
    // TWD EXT FIFO INTERFACE
    //***************************************
    output logic 			   twd_ext_trans_o,
    
    output logic 			   twd_ext_alloc_req_o,
    input logic 			   twd_ext_alloc_gnt_i,
    input logic [TWD_QUEUE_ADD_WIDTH-1:0]  twd_ext_alloc_add_i,
    
    output logic 			   twd_ext_queue_req_o,
    output logic [TWD_QUEUE_ADD_WIDTH-1:0] twd_ext_queue_add_o,
    output logic [TWD_COUNT_WIDTH-1:0] 	   twd_ext_queue_count_o,
    output logic [TWD_STRIDE_WIDTH-1:0]    twd_ext_queue_stride_o,
    output logic [TRANS_SID_WIDTH-1:0] 	   twd_ext_queue_sid_o,
    
    // TWD TCDM FIFO INTERFACE
    //***************************************
    output logic 			   twd_tcdm_trans_o,
    
    output logic 			   twd_tcdm_alloc_req_o,
    input logic 			   twd_tcdm_alloc_gnt_i,
    input logic [TWD_QUEUE_ADD_WIDTH-1:0]  twd_tcdm_alloc_add_i,
    
    output logic 			   twd_tcdm_queue_req_o,
    output logic [TWD_QUEUE_ADD_WIDTH-1:0] twd_tcdm_queue_add_o,
    output logic [TWD_COUNT_WIDTH-1:0] 	   twd_tcdm_queue_count_o,
    output logic [TWD_STRIDE_WIDTH-1:0]    twd_tcdm_queue_stride_o,
    output logic [TRANS_SID_WIDTH-1:0] 	   twd_tcdm_queue_sid_o,
    
    // TRANSFER BUFFER INTERFACE
    //***************************************
    // RETRIVE SID SIGNALS
    output logic 			   trans_alloc_req_o,
    input logic 			   trans_alloc_gnt_i,
    input logic [TRANS_SID_WIDTH-1:0] 	   trans_alloc_ret_i,
    // CLEAR SID SIGNALS
    output logic [NB_TRANSFERS-1:0] 	   trans_alloc_clr_o,
    // ALLOC STATUS SIGNALS
    input logic [NB_TRANSFERS-1:0] 	   trans_alloc_status_i,
    
    // TRANSFERS STATUS
    input logic [NB_TRANSFERS-1:0] 	   trans_status_i,
    
    output logic 			   busy_o
    
    );
   
   enum 				   `ifdef TARGET_SYNTHESIS logic [4:0] `endif { IDLE, STATUS_GRANTED, RET_ID_GRANTED, CLR_ID_GRANTED, CMD, CMD_GRANTED, TCDM, TCDM_GRANTED, EXT, EXT_GRANTED, TWD_EXT_COUNT, TWD_EXT_COUNT_GRANTED, TWD_EXT_STRIDE, TWD_EXT_STRIDE_GRANTED, TWD_TCDM_COUNT, TWD_TCDM_COUNT_GRANTED, TWD_TCDM_STRIDE, TWD_TCDM_STRIDE_GRANTED, BUSY, BUSY2 } CS, NS;
   
   logic [TWD_QUEUE_ADD_WIDTH-1:0] 	   s_twd_ext_add,s_twd_tcdm_add;
   logic 				   s_twd_ext_trans,s_twd_tcdm_trans;
   logic [TWD_COUNT_WIDTH:0] 	           s_twd_ext_count,s_twd_tcdm_count;
   logic 				   s_twd_ext_count_en,s_twd_tcdm_count_en;
   logic [TRANS_SID_WIDTH-1:0] 		   s_trans_sid;
   logic 				   s_arb_barrier;
   
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
	
	ctrl_targ_r_valid_o  = 1'b0;
	ctrl_targ_r_data_o   = '0;
	ctrl_targ_gnt_o      = 1'b0;
	trans_alloc_req_o    = 1'b0;
	trans_alloc_clr_o    = 1'b0;
	cmd_req_o            = 1'b0;
	tcdm_req_o           = 1'b0;
	ext_req_o            = 1'b0;
	twd_ext_alloc_req_o  = 1'b0;
	twd_tcdm_alloc_req_o = 1'b0;
	twd_ext_queue_req_o  = 1'b0;
	twd_tcdm_queue_req_o = 1'b0;
	busy_o               = 1'b1;
	s_twd_ext_count_en   = 1'b0;
	s_twd_tcdm_count_en  = 1'b0;
	
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
				     case ({cmd_twd_ext_o,cmd_twd_tcdm_o})
				       
				       2'b00: // NOT A  2D TRANSFER
					 begin 
					    NS              = CMD_GRANTED;
					    ctrl_targ_gnt_o = 1'b1;
					    cmd_req_o       = 1'b1;
					 end
				       
				       2'b01:
					 begin
					    begin
					       twd_tcdm_alloc_req_o = 1'b1;
					       if ( twd_tcdm_alloc_gnt_i == 1'b1 ) // THE TWD TCDM CMD FIFO IS NOT FULL
						 begin
						    ctrl_targ_gnt_o = 1'b1;
						    cmd_req_o       = 1'b1;
						    NS              = CMD_GRANTED;
						 end
					    else // THE TWD TCDM CMD FIFO IS FULL: STALL
					      begin
						 ctrl_targ_gnt_o = 1'b0;
						 cmd_req_o       = 1'b0;
						 NS              = IDLE;
					      end
					    end
					 end
				       
				       2'b10:
					 begin
					    twd_ext_alloc_req_o = 1'b1;
					    if ( twd_ext_alloc_gnt_i == 1'b1 ) // THE TWD EXT CMD FIFO IS NOT FULL
					      begin
						 ctrl_targ_gnt_o = 1'b1;
						 cmd_req_o       = 1'b1;
						 NS              = CMD_GRANTED;
					      end
					    else // THE TWD EXT CMD FIFO IS FULL: STALL
					      begin
						 ctrl_targ_gnt_o = 1'b0;
						 cmd_req_o       = 1'b0;
						 NS              = IDLE;
					      end
					 end
				       
				       2'b11:
					 begin
					    twd_ext_alloc_req_o  = 1'b1;
					    twd_tcdm_alloc_req_o = 1'b1;
					    if ( ( twd_ext_alloc_gnt_i == 1'b1 ) & ( twd_tcdm_alloc_gnt_i == 1'b1 ) ) // THE TWD EXT CMD FIFO IS NOT FULL
					      begin
						 ctrl_targ_gnt_o = 1'b1;
						 cmd_req_o       = 1'b1;
						 NS              = CMD_GRANTED;
					      end
					    else // THE TWD EXT CMD FIFO IS FULL: STALL
					      begin
						 ctrl_targ_gnt_o = 1'b0;
						 cmd_req_o       = 1'b0;
						 NS              = IDLE;
					      end
					 end
				       
				       default:
					 begin  // NOT A  2D TRANSFER
					    NS              = CMD_GRANTED;
					    ctrl_targ_gnt_o = 1'b1;
					    cmd_req_o       = 1'b1;
					 end
				       
				     endcase
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
			 case ({cmd_twd_ext_o,cmd_twd_tcdm_o})
			   
			   2'b00: // NOT A  2D TRANSFER
			     begin 
				NS              = CMD_GRANTED;
				ctrl_targ_gnt_o = 1'b1;
				cmd_req_o       = 1'b1;
			     end
			   
			   2'b01:
			     begin
				begin
				   twd_tcdm_alloc_req_o = 1'b1;
				   if ( twd_tcdm_alloc_gnt_i == 1'b1 ) // THE TWD TCDM CMD FIFO IS NOT FULL
				     begin
					ctrl_targ_gnt_o = 1'b1;
					cmd_req_o       = 1'b1;
					NS              = CMD_GRANTED;
				     end
				   else // THE TWD TCDM CMD FIFO IS FULL: STALL
				     begin
					ctrl_targ_gnt_o = 1'b0;
					cmd_req_o       = 1'b0;
					NS              = IDLE;
				     end
				end
			     end
			   
			   2'b10:
			     begin
				twd_ext_alloc_req_o = 1'b1;
				if ( twd_ext_alloc_gnt_i == 1'b1 ) // THE TWD EXT CMD FIFO IS NOT FULL
				  begin
				     ctrl_targ_gnt_o = 1'b1;
				     cmd_req_o       = 1'b1;
				     NS              = CMD_GRANTED;
				  end
				else // THE TWD EXT CMD FIFO IS FULL: STALL
				  begin
				     ctrl_targ_gnt_o = 1'b0;
				     cmd_req_o       = 1'b0;
				     NS              = IDLE;
				  end
			     end
			   
			   2'b11:
			     begin
				twd_ext_alloc_req_o  = 1'b1;
				twd_tcdm_alloc_req_o = 1'b1;
				if ( ( twd_ext_alloc_gnt_i == 1'b1 ) & ( twd_tcdm_alloc_gnt_i == 1'b1 ) ) // THE TWD EXT CMD FIFO IS NOT FULL
				  begin
				     ctrl_targ_gnt_o = 1'b1;
				     cmd_req_o       = 1'b1;
				     NS              = CMD_GRANTED;
				  end
				else // THE TWD EXT CMD FIFO IS FULL: STALL
				  begin
				     ctrl_targ_gnt_o = 1'b0;
				     cmd_req_o       = 1'b0;
				     NS              = IDLE;
				  end
			     end
			   
			   default:
			     begin  // NOT A  2D TRANSFER
				NS              = CMD_GRANTED;
				ctrl_targ_gnt_o = 1'b1;
				cmd_req_o       = 1'b1;
			     end
			   
			 endcase
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
			 case ({cmd_twd_ext_o,cmd_twd_tcdm_o})
			   
			   2'b00: // NOT A  2D TRANSFER
			     begin 
				NS              = CMD_GRANTED;
				ctrl_targ_gnt_o = 1'b1;
				cmd_req_o       = 1'b1;
			     end
			   
			   2'b01:
			     begin
				begin
				   twd_tcdm_alloc_req_o = 1'b1;
				   if ( twd_tcdm_alloc_gnt_i == 1'b1 ) // THE TWD TCDM CMD FIFO IS NOT FULL
				     begin
					ctrl_targ_gnt_o = 1'b1;
					cmd_req_o       = 1'b1;
					NS              = CMD_GRANTED;
				     end
				   else // THE TWD TCDM CMD FIFO IS FULL: STALL
				     begin
					ctrl_targ_gnt_o = 1'b0;
					cmd_req_o       = 1'b0;
					NS              = IDLE;
				     end
				end
			     end
			   
			   2'b10:
			     begin
				twd_ext_alloc_req_o = 1'b1;
				if ( twd_ext_alloc_gnt_i == 1'b1 ) // THE TWD EXT CMD FIFO IS NOT FULL
				  begin
				     ctrl_targ_gnt_o = 1'b1;
				     cmd_req_o       = 1'b1;
				     NS              = CMD_GRANTED;
				  end
				else // THE TWD EXT CMD FIFO IS FULL: STALL
				  begin
				     ctrl_targ_gnt_o = 1'b0;
				     cmd_req_o       = 1'b0;
				     NS              = IDLE;
				  end
			     end
			   
			   2'b11:
			     begin
				twd_ext_alloc_req_o  = 1'b1;
				twd_tcdm_alloc_req_o = 1'b1;
				if ( ( twd_ext_alloc_gnt_i == 1'b1 ) & ( twd_tcdm_alloc_gnt_i == 1'b1 ) ) // THE TWD EXT CMD FIFO IS NOT FULL
				  begin
				     ctrl_targ_gnt_o = 1'b1;
				     cmd_req_o       = 1'b1;
				     NS              = CMD_GRANTED;
				  end
				else // THE TWD EXT CMD FIFO IS FULL: STALL
				  begin
				     ctrl_targ_gnt_o = 1'b0;
				     cmd_req_o       = 1'b0;
				     NS              = IDLE;
				  end
			     end
			   
			   default:
			     begin  // NOT A  2D TRANSFER
				NS              = CMD_GRANTED;
				ctrl_targ_gnt_o = 1'b1;
				cmd_req_o       = 1'b1;
			     end
			   
			 endcase
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
			 if ( s_twd_ext_trans == 1'b1 ) // IT'S A TWD EXT TRANSFER
			   begin
			      s_twd_ext_count_en  = 1'b1;
			      ctrl_targ_gnt_o     = 1'b1;
			      NS                  = TWD_EXT_COUNT_GRANTED;
			   end
			 else // NOT A TWD EXT TRANSFER
			   begin
			      if ( s_twd_tcdm_trans == 1'b1 ) // IT'S A TWD TCDM TRANSFER
				begin
				   s_twd_tcdm_count_en = 1'b1;
				   ctrl_targ_gnt_o     = 1'b1;
				   NS                  = TWD_TCDM_COUNT_GRANTED;
				end
			      else // NOT A 2D TRANSFER
				begin
				   NS = BUSY;
				end
			   end
		      end
		    else // ERROR READ OPERATION OR WRITE OPERATION AT WRONG ADDRESS
		      begin
			 NS = BUSY;
		      end
		 end
	       else // NOT A REQUEST
		 begin
		    if ( s_twd_ext_trans == 1'b1 ) // IT'S A TWD EXT TRANSFER
		      begin
			 NS = TWD_EXT_COUNT;
		      end
		    else
		      begin
			 if ( s_twd_tcdm_trans == 1'b1 ) // IT'S A TWD TCDM TRANSFER
			   begin
			      NS = TWD_TCDM_COUNT;
			   end
			 else
			   begin
				NS = BUSY;
			   end
		      end
		 end
	    end
	  
	  TWD_EXT_COUNT:
	    begin
	       if ( ctrl_targ_req_i == 1'b1 )
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 ctrl_targ_gnt_o    = 1'b1;
			 s_twd_ext_count_en = 1'b1;
			 NS                 = TWD_EXT_COUNT_GRANTED;
		      end
		    else // WRONG ADDRESS/POLARITY
		      begin
			 NS = IDLE; // ERROR
		      end
		 end
	       else
		 begin
		    NS = TWD_EXT_COUNT;
		 end
	    end
	  
	  TWD_EXT_COUNT_GRANTED:
	    begin
	       ctrl_targ_r_valid_o = 1'b1;
	       if ( ctrl_targ_req_i == 1'b1 )
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 ctrl_targ_gnt_o     = 1'b1;
			 twd_ext_queue_req_o = 1'b1;
			 NS                  = TWD_EXT_STRIDE_GRANTED;
		      end
		    else // WRONG ADDRESS/POLARITY
		      begin
			 NS = IDLE; // ERROR
		      end
		 end
	       else
		 begin
		    NS = TWD_EXT_STRIDE;
		 end
	    end
	  
	  TWD_EXT_STRIDE:
	    begin
	       if ( ctrl_targ_req_i == 1'b1 ) // TWD ADDR FIFO NOT FULL
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 ctrl_targ_gnt_o     = 1'b1;
			 twd_ext_queue_req_o = 1'b1;
			 NS                  = TWD_EXT_STRIDE_GRANTED;
		      end
		    else
		      begin // WRONG ADDRESS/POLARITY
			 NS = IDLE; // ERROR
		      end
		 end
	       else
		 begin
		    NS = TWD_EXT_STRIDE;
		 end
	    end
	  
	  TWD_EXT_STRIDE_GRANTED:
	    begin
	       ctrl_targ_r_valid_o = 1'b1;
	       if ( ctrl_targ_req_i == 1'b1 )
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 if ( s_twd_tcdm_trans == 1'b1 ) // IT'S A TWD TCDM TRANSFER
			   begin
			      ctrl_targ_gnt_o      = 1'b1;
			      s_twd_tcdm_count_en  = 1'b1;
			      NS                   = TWD_TCDM_COUNT_GRANTED;
			   end
			 else // NOT A TWD TCDM TRANSFER
			   begin
			      NS = BUSY;
			   end
		      end
		    else // ERROR READ OPERATION OR WRITE OPERATION AT WRONG ADDRESS
		      begin
			 NS = BUSY;
		      end
		 end
	       else // NOT A REQUEST
		 begin
		    if ( s_twd_tcdm_trans == 1'b1 ) // IT'S A TWD TCDM TRANSFER
		      begin
			 NS = TWD_TCDM_COUNT;
		      end
		    else
		      begin
			 NS = BUSY;
		      end
		 end
	    end
	  
	  TWD_TCDM_COUNT:
	    begin
	       if ( ctrl_targ_req_i == 1'b1 ) // TWD ADDR FIFO NOT FULL
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 ctrl_targ_gnt_o     = 1'b1;
			 s_twd_tcdm_count_en = 1'b1;
			 NS                  = TWD_TCDM_COUNT_GRANTED;
		      end
		    else
		      begin // WRONG ADDRESS/POLARITY
			 NS = IDLE; // ERROR
		      end
		 end
	       else
		 begin
		    NS              = TWD_TCDM_COUNT;
		 end
	    end
	  
	  TWD_TCDM_COUNT_GRANTED:
	    begin
	       ctrl_targ_r_valid_o = 1'b1;
	       if ( ctrl_targ_req_i == 1'b1 )
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 ctrl_targ_gnt_o      = 1'b1;
			 twd_tcdm_queue_req_o = 1'b1;
			 NS                   = TWD_TCDM_STRIDE_GRANTED;
		      end
		    else // ERROR READ OPERATION OR WRITE OPERATION AT WRONG ADDRESS
		      begin
			 NS = BUSY;
		      end
		 end
	       else // NOT A REQUEST
		 begin
		    NS = TWD_TCDM_STRIDE;
		 end
	    end
	  
	  TWD_TCDM_STRIDE:
	    begin
	       if ( ctrl_targ_req_i == 1'b1 )
		 begin
		    if( ctrl_targ_type_i == 1'b0 && ctrl_targ_add_i[3:2] == `MCHAN_CMD_ADDR )
		      begin
			 ctrl_targ_gnt_o      = 1'b1;
			 twd_tcdm_queue_req_o = 1'b1;
			 NS                   = TWD_TCDM_STRIDE_GRANTED;
		      end
		    else // ERROR READ OPERATION OR WRITE OPERATION AT WRONG ADDRESS
		      begin
			 NS = BUSY;
		      end
		 end
	       else // NOT A REQUEST
		 begin
		    NS = TWD_TCDM_STRIDE;
		 end
	    end
	  
	  TWD_TCDM_STRIDE_GRANTED:
	    begin
	       ctrl_targ_r_valid_o = 1'b1;
	       NS                  = BUSY;
	    end
	  
	  BUSY:
	    begin
	       if( s_arb_barrier == 1'b0 )
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
   
   // REGISTER TO STORE PE ID
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     ctrl_targ_r_id_o <= 1'b0;
	  end
	else
	  begin
	     if( ctrl_targ_req_i == 1'b1 && ctrl_targ_gnt_o == 1'b1 )
	       begin
		  ctrl_targ_r_id_o <= ctrl_targ_id_i;
	       end
	  end
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
   
   // REGISTER TO STORE TWD EXT ADDRESS
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     s_twd_ext_add <= 1'b0;
	  end
	else
	  begin
	     if(twd_ext_alloc_req_o == 1'b1 && twd_ext_alloc_gnt_i == 1'b1)
	       begin
		  s_twd_ext_add <= twd_ext_alloc_add_i;
	       end
	  end
     end
   
   // REGISTER TO STORE TWD TCDM ADDRESS
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     s_twd_tcdm_add <= 1'b0;
	  end
	else
	  begin
	     if(twd_tcdm_alloc_req_o == 1'b1 && twd_tcdm_alloc_gnt_i == 1'b1)
	       begin
		  s_twd_tcdm_add <= twd_tcdm_alloc_add_i;
	       end
	  end
     end
   
   // REGISTER TO INTERNALLY STORE EXT TWD TRANSFER STATUS BIT
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     s_twd_ext_trans <= 1'b0;
	  end
	else
	  begin
	     if (cmd_req_o == 1'b1 && cmd_gnt_i == 1'b1 && cmd_twd_ext_o == 1'b1)
	       begin
		  s_twd_ext_trans <= 1'b1;
	       end
	     else
	       begin
		  if (twd_ext_queue_req_o == 1'b1)
		    begin
		       s_twd_ext_trans <= 1'b0;
		    end
	       end
	  end
     end
    
   // REGISTER TO INTERNALLY STORE TCDM TWD TRANSFER STATUS BIT
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     s_twd_tcdm_trans <= 1'b0;
	  end
	else
	  begin
	     if (cmd_req_o == 1'b1 && cmd_gnt_i == 1'b1 && cmd_twd_tcdm_o == 1'b1)
	       begin
		  s_twd_tcdm_trans <= 1'b1;
	       end
	     else
	       begin
		  if (twd_tcdm_queue_req_o == 1'b1)
		    begin
		       s_twd_tcdm_trans <= 1'b0;
		    end
	       end
	  end
     end

   // TWD EXT COUNT REG
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     s_twd_ext_count <= '0;
	  end
	else
	  begin
	     if ( s_twd_ext_count_en == 1'b1 )
	       begin
		  s_twd_ext_count <= ctrl_targ_data_i[TWD_COUNT_WIDTH:0];
	       end
	  end
     end
   
   // TWD TCDM COUNT REG
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     s_twd_tcdm_count <= '0;
	  end
	else
	  begin
	     if ( s_twd_tcdm_count_en == 1'b1 )
	       begin
		  s_twd_tcdm_count <= ctrl_targ_data_i[TWD_COUNT_WIDTH:0];
	       end
	  end
     end
   
   // REGISTER TO INTERNALLY STORE ARBITER BARRIER (BE SURE THAT THE COMMAND IS ARBITRATED AND SUBMITTED BEFORE A NEW TRANSACTION IS ENQUEUED)
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
	if(rst_ni == 1'b0)
	  begin
	     s_arb_barrier <= 1'b0;
	  end
	else
	  begin
	     if (cmd_req_o == 1'b1 && cmd_gnt_i == 1'b1)
	       begin
		  s_arb_barrier <= 1'b1;
	       end
	     else
	       begin
		  if ( ( arb_req_i == 1'b1 ) && ( arb_gnt_i == 1'b1 ) && ( arb_sid_i == s_trans_sid ) )
		    begin
		       s_arb_barrier <= 1'b0;
		    end
	       end
	  end
     end
   
   assign cmd_len_o               = ctrl_targ_data_i[MCHAN_LEN_WIDTH-1:0				] - 1;  // TRANSFER LENGTH
   assign cmd_opc_o               = ctrl_targ_data_i[MCHAN_LEN_WIDTH  :MCHAN_LEN_WIDTH  ]; // TRANSFER OPCODE
   assign cmd_inc_o               = ctrl_targ_data_i[MCHAN_LEN_WIDTH+1:MCHAN_LEN_WIDTH+1]; // INCREMENTAL TRANSFER
   assign cmd_twd_ext_o           = ctrl_targ_data_i[MCHAN_LEN_WIDTH+2:MCHAN_LEN_WIDTH+2]; // 2D TRANSFER ON EXT SIDE
   assign cmd_ele_o               = ctrl_targ_data_i[MCHAN_LEN_WIDTH+3:MCHAN_LEN_WIDTH+3]; // EVENT LINES ENABLE
   assign cmd_ile_o               = ctrl_targ_data_i[MCHAN_LEN_WIDTH+4:MCHAN_LEN_WIDTH+4]; // INTERRUPT LINES ENABLE
   assign cmd_ble_o               = ctrl_targ_data_i[MCHAN_LEN_WIDTH+5:MCHAN_LEN_WIDTH+5]; // BROADCAST LINES ENABLE
   assign cmd_twd_tcdm_o          = ctrl_targ_data_i[MCHAN_LEN_WIDTH+6:MCHAN_LEN_WIDTH+6]; // 2D TRANSFER ON TCDM SIDE
   assign cmd_twd_ext_add_o       = twd_ext_alloc_add_i;
   assign cmd_twd_tcdm_add_o      = twd_tcdm_alloc_add_i;
   assign cmd_sid_o               = s_trans_sid;
   
   assign tcdm_add_o              = ctrl_targ_data_i[TCDM_ADD_WIDTH-1:0];
   assign ext_add_o               = ctrl_targ_data_i[EXT_ADD_WIDTH-1:0];
   
   assign twd_ext_queue_count_o   = s_twd_ext_count[TWD_COUNT_WIDTH:0]-1;
   assign twd_ext_queue_stride_o  = ctrl_targ_data_i[TWD_STRIDE_WIDTH:0]-1;
   assign twd_ext_queue_add_o     = s_twd_ext_add;
   assign twd_ext_queue_sid_o     = s_trans_sid;
   assign twd_ext_trans_o         = s_twd_ext_trans;
   
   assign twd_tcdm_queue_count_o  = s_twd_tcdm_count[TWD_COUNT_WIDTH:0]-1;
   assign twd_tcdm_queue_stride_o = ctrl_targ_data_i[TWD_STRIDE_WIDTH:0]-1;
   assign twd_tcdm_queue_add_o    = s_twd_tcdm_add;
   assign twd_tcdm_queue_sid_o    = s_trans_sid;
   assign twd_tcdm_trans_o        = s_twd_tcdm_trans;
   
   assign ctrl_targ_r_opc_o       = 1'b0;
   
endmodule
