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

module twd_trans_splitter
  #(
    // OVERRIDDEN FROM TOP
    parameter TRANS_SID_WIDTH    = 1,
    parameter TCDM_ADD_WIDTH     = 12,
    parameter EXT_ADD_WIDTH      = 29,
    parameter MCHAN_BURST_LENGTH = 64,
    parameter TWD_COUNT_WIDTH    = 16,
    parameter TWD_STRIDE_WIDTH   = 16,
    
    // DEFINED IN MCHAN_DEFINES
    parameter MCHAN_OPC_WIDTH = `MCHAN_OPC_WIDTH,
    parameter MCHAN_LEN_WIDTH = `MCHAN_LEN_WIDTH,
    parameter TCDM_OPC_WIDTH  = `TCDM_OPC_WIDTH,
    parameter EXT_OPC_WIDTH   = `EXT_OPC_WIDTH
    )
   (
    
    input  logic                          clk_i,
    input  logic                          rst_ni,
    
    input  logic                          mchan_req_i,
    output logic                          mchan_gnt_o,
    input  logic [TRANS_SID_WIDTH-1:0]    mchan_sid_i,
    input  logic [MCHAN_OPC_WIDTH-1:0]    mchan_opc_i,
    input  logic [MCHAN_LEN_WIDTH-1:0]    mchan_len_i,
    input  logic                          mchan_inc_i,
    input  logic                          mchan_twd_i,
    input  logic [TWD_COUNT_WIDTH-1:0]    mchan_count_i,
    input  logic [TWD_STRIDE_WIDTH-1:0]   mchan_stride_i,
    input  logic [TCDM_ADD_WIDTH-1:0]     mchan_tcdm_add_i,
    input  logic [EXT_ADD_WIDTH-1:0]      mchan_ext_add_i,
    
    output logic                          mchan_req_o,
    input  logic                          mchan_gnt_i,
    output logic [TRANS_SID_WIDTH-1:0]    mchan_sid_o,
    output logic [MCHAN_OPC_WIDTH-1:0]    mchan_opc_o,
    output logic [MCHAN_LEN_WIDTH-1:0]    mchan_len_o,
    output logic                          mchan_inc_o,
    output logic [TCDM_ADD_WIDTH-1:0]     mchan_tcdm_add_o,
    output logic [EXT_ADD_WIDTH-1:0]      mchan_ext_add_o
    
    );
   
   // MCHAN TWD QUEUE SIGNALS
   logic [TRANS_SID_WIDTH-1:0] 		  s_mchan_sid;
   logic [MCHAN_OPC_WIDTH-1:0] 		  s_mchan_opc;
   logic [MCHAN_LEN_WIDTH-1:0] 		  s_mchan_len;
   logic                                  s_mchan_inc;
   logic                                  s_mchan_twd;
   logic [TWD_COUNT_WIDTH-1:0] 		  s_mchan_count,s_mchan_count_inc;
   logic [TWD_STRIDE_WIDTH-1:0] 	  s_mchan_stride,s_mchan_stride_inc;
   logic [TCDM_ADD_WIDTH-1:0] 		  s_mchan_tcdm_add;
   logic [EXT_ADD_WIDTH-1:0] 		  s_mchan_ext_add;
   
   logic [MCHAN_LEN_WIDTH-1:0] 		  s_mchan_rem_len;
   logic [MCHAN_LEN_WIDTH-1:0] 		  s_mchan_cur_len;
   
   logic 				  s_trans_complete;
   
   // FSM STATES SIGNALS
   enum 				  `ifdef SYNTHESIS logic [1:0] `endif { TRANS_IDLE, TRANS_RUN, TRANS_TWD } CS, NS;
   
   //**********************************************************
   //***** SAMPLES THE OPCODE, SID OF CURRENT TRANSFER ********
   //**********************************************************
   
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
	if (rst_ni == 1'b0)
	  begin
	     s_mchan_count  <= 0;
	     s_mchan_stride <= 0;
	     s_mchan_opc    <= 0;
	     s_mchan_sid    <= 0;
	     s_mchan_inc    <= 0;
	     s_mchan_len    <= 0;
	     s_mchan_twd    <= 0;
	  end
	else
	  begin
	     if ( mchan_req_i == 1'b1 && mchan_gnt_o == 1'b1 ) // SAMPLES DATA AT THE BEGINNING OF EACH MCHAN TRANSFER
	       begin
		  s_mchan_opc    <= mchan_opc_i;    // MCHAN OPCODE (TX/RX)
		  s_mchan_sid    <= mchan_sid_i;    // SID OF CURRENT MCHAN TRANSFER
		  s_mchan_inc    <= mchan_inc_i;    // INCREMENTAL TRANSFER
		  s_mchan_len    <= mchan_len_i;    // TRANSFER LENGTH
		  s_mchan_count  <= mchan_count_i;  // 2D COUNT
		  s_mchan_stride <= mchan_stride_i; // 2D STRIDE
		  s_mchan_twd    <= mchan_twd_i;
	       end
	  end
     end
   
   //**********************************************************
   //***** COMPUTES THE LENGTH OF CURRNT TRANSACTION **********
   //**********************************************************
   
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
	if (rst_ni == 1'b0)
	  begin
	     s_mchan_cur_len  <= 0;  // LENGTH OF CURRENT TWD TRANSACTION
	     s_mchan_rem_len  <= 0;  // REMAINING LENGHT OF CURRENT TWD TRANS
	  end
	else
	  begin
	     if ( mchan_req_i == 1 && mchan_gnt_o == 1 )
	       begin
		  if ( mchan_len_i <=  mchan_count_i )
		    begin
		       s_mchan_rem_len  <= mchan_len_i;
		       s_mchan_cur_len  <= mchan_len_i;
		    end
		  else
		    begin
		       s_mchan_rem_len  <= mchan_len_i;
		       s_mchan_cur_len  <= mchan_count_i;
		    end
	       end
	     else
	       begin
		  if ( mchan_req_o == 1'b1 && mchan_gnt_i == 1'b1 )
		    begin
		       if ( (s_mchan_rem_len <= s_mchan_count) )
			 begin
			    s_mchan_cur_len  <= s_mchan_rem_len;
			    s_mchan_rem_len  <= s_mchan_rem_len;
			 end
		       else
			 begin
			    s_mchan_cur_len <= s_mchan_count;
			    s_mchan_rem_len <= s_mchan_rem_len - s_mchan_count_inc;
			 end
		    end
		  else
		    begin
		       s_mchan_cur_len  <= s_mchan_cur_len;
		       s_mchan_rem_len  <= s_mchan_rem_len;
		    end
	       end
	  end
     end
   
   always_comb
     begin
	if ( ( s_mchan_rem_len <= s_mchan_count ) )
	  begin
	     s_trans_complete = 1;
	  end
	else
	  begin
	     s_trans_complete = 0;
	  end
     end
   
   //**********************************************************
   //****** COMPUTES THE TCDM ADDRESS OF CURRENT TRANSACTION **
   //**********************************************************
   
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
	if (rst_ni == 1'b0)
	  begin
	     s_mchan_tcdm_add <= '0;
	  end
	else
	  begin
	     if ( mchan_req_i == 1'b1 && mchan_gnt_o == 1'b1 ) // FIRST 2D TRANSFER
	       begin
		  s_mchan_tcdm_add <= mchan_tcdm_add_i;
	       end
	     else
	       begin
		  if ( mchan_req_o == 1'b1 && mchan_gnt_i == 1'b1 ) // ON GOING 2D TRANSFRER
		    begin
		       s_mchan_tcdm_add <= s_mchan_tcdm_add + s_mchan_cur_len + 1;
		    end
		  else
		    begin
		       s_mchan_tcdm_add <= s_mchan_tcdm_add;
		    end
	       end
	  end
     end
   
   //**********************************************************
   //****** COMPUTES THE EXT ADDRESS OF CURRENT TRANSACTION ***
   //**********************************************************
   
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
	if (rst_ni == 1'b0)
	  begin
	     s_mchan_ext_add <= '0;
	  end
	else
	  begin
	     if ( mchan_req_i == 1'b1 && mchan_gnt_o == 1'b1 ) // FIRST 2D TRANSFER
	       begin
		  s_mchan_ext_add <= mchan_ext_add_i;
	       end
	     else
	       begin
		  if ( mchan_req_o == 1'b1 && mchan_gnt_i == 1'b1 ) // ON GOING 2D TRANSFRER
		    begin
		       s_mchan_ext_add <= s_mchan_ext_add + s_mchan_stride_inc;
		    end
		  else
		    begin
		       s_mchan_ext_add <= s_mchan_ext_add;
		    end
	       end
	  end
     end
   
   //**********************************************************
   //********** FINITE STATE MACHINE FOR CMD QUEUE ************
   //**********************************************************
   
   // UPDATE THE STATE
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
	
	mchan_gnt_o      = 1;
	mchan_req_o      = 0;
	mchan_opc_o      = 0;
	mchan_len_o      = 0;
	mchan_sid_o      = 0;
	mchan_inc_o      = 0;
	mchan_tcdm_add_o = 0;
	mchan_ext_add_o  = 0;
	
	case(CS)
	  
	  TRANS_IDLE:
	    begin
	       if ( mchan_req_i == 1'b1 && mchan_gnt_i == 1'b1 )
		 begin
		    NS = TRANS_RUN;
		 end
	       else
		 begin
		    NS = TRANS_IDLE;
		    mchan_gnt_o      = 0;
		 end
	    end
	  
	  TRANS_RUN:
	    begin
	       mchan_gnt_o      = 0;
	       mchan_opc_o      = s_mchan_opc;
	       mchan_len_o      = s_mchan_cur_len;
	       mchan_sid_o      = s_mchan_sid;
	       mchan_inc_o      = s_mchan_inc;
	       mchan_tcdm_add_o = s_mchan_tcdm_add;
	       mchan_ext_add_o  = s_mchan_ext_add;
	       
	       if ( mchan_gnt_i == 1'b1 )
		 begin
		    mchan_req_o = 1'b1;
		    if ( s_trans_complete == 1'b1 || s_mchan_twd == 1'b0 )
		      begin
			 mchan_len_o = s_mchan_rem_len;
			 NS          = TRANS_IDLE;
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
	    NS = TRANS_IDLE;
	  
	endcase
     end
   
   //**********************************************************
   //********** STRIDE AND COUNT NORMALIZATION ****************
   //**********************************************************
   
   assign s_mchan_count_inc  = s_mchan_count + 1;
   assign s_mchan_stride_inc = s_mchan_stride + 1;
   
endmodule
