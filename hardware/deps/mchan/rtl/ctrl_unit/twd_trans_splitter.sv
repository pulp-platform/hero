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
    
    input logic 		       clk_i,
    input logic 		       rst_ni,
    
    input logic 		       mchan_req_i,
    output logic 		       mchan_gnt_o,
    input logic [TRANS_SID_WIDTH-1:0]  mchan_sid_i,
    input logic [MCHAN_OPC_WIDTH-1:0]  mchan_opc_i,
    input logic [MCHAN_LEN_WIDTH-1:0]  mchan_len_i,
    input logic 		       mchan_inc_i,
    input logic 		       mchan_twd_ext_i,
    input logic 		       mchan_twd_tcdm_i,
    input logic [TWD_COUNT_WIDTH-1:0]  mchan_ext_count_i,
    input logic [TWD_STRIDE_WIDTH-1:0] mchan_ext_stride_i,
    input logic [TWD_COUNT_WIDTH-1:0]  mchan_tcdm_count_i,
    input logic [TWD_STRIDE_WIDTH-1:0] mchan_tcdm_stride_i,
    input logic [TCDM_ADD_WIDTH-1:0]   mchan_tcdm_add_i,
    input logic [EXT_ADD_WIDTH-1:0]    mchan_ext_add_i,
    
    output logic 		       mchan_req_o,
    input logic 		       mchan_gnt_i,
    output logic [TRANS_SID_WIDTH-1:0] mchan_sid_o,
    output logic [MCHAN_OPC_WIDTH-1:0] mchan_opc_o,
    output logic [MCHAN_LEN_WIDTH-1:0] mchan_len_o,
    output logic 		       mchan_inc_o,
    output logic [TCDM_ADD_WIDTH-1:0]  mchan_tcdm_add_o,
    output logic [EXT_ADD_WIDTH-1:0]   mchan_ext_add_o
    
    );
   
   // MCHAN TWD QUEUE SIGNALS
   logic [TRANS_SID_WIDTH-1:0] 		  s_mchan_sid;
   logic [MCHAN_OPC_WIDTH-1:0] 		  s_mchan_opc;
   logic [MCHAN_LEN_WIDTH-1:0] 		  s_mchan_len;
   logic                                  s_mchan_inc;
   logic                                  s_mchan_twd_ext;
   logic                                  s_mchan_twd_tcdm;
   logic [TWD_COUNT_WIDTH-1:0] 		  s_mchan_ext_count;
   logic [TWD_STRIDE_WIDTH-1:0] 	  s_mchan_ext_stride;
   logic [TWD_COUNT_WIDTH-1:0] 		  s_mchan_tcdm_count;
   logic [TWD_STRIDE_WIDTH-1:0] 	  s_mchan_tcdm_stride;
   logic [TCDM_ADD_WIDTH-1:0] 		  s_mchan_tcdm_add, s_mchan_tcdm_base_add;
   logic [EXT_ADD_WIDTH-1:0] 		  s_mchan_ext_add, s_mchan_ext_base_add;
   
   logic [MCHAN_LEN_WIDTH-1:0] 		  s_mchan_rem_len, s_ext_rem_len, s_tcdm_rem_len;
   logic [MCHAN_LEN_WIDTH-1:0] 		  s_mchan_cur_len;
   
   logic 				  s_ext_len_smaller, s_tcdm_len_smaller;
   
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
	     s_mchan_opc         <= 0;
	     s_mchan_sid         <= 0;
	     s_mchan_inc         <= 0;
	     s_mchan_len         <= 0;
	     s_mchan_twd_ext     <= 0;
	     s_mchan_twd_tcdm    <= 0;
	  end
	else
	  begin
	     if ( mchan_req_i == 1'b1 && mchan_gnt_o == 1'b1 ) // SAMPLES DATA AT THE BEGINNING OF EACH MCHAN TRANSFER
	       begin
		  s_mchan_opc      <= mchan_opc_i;      // MCHAN OPCODE (TX/RX)
		  s_mchan_sid      <= mchan_sid_i;      // SID OF CURRENT MCHAN TRANSFER
		  s_mchan_inc      <= mchan_inc_i;      // INCREMENTAL TRANSFER
		  s_mchan_len      <= mchan_len_i;      // TRANSFER LENGTH
		  s_mchan_twd_ext  <= mchan_twd_ext_i;  // 2D EXT
		  s_mchan_twd_tcdm <= mchan_twd_tcdm_i; // 2D TCDM
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
	     s_mchan_rem_len        <= 0;
	     s_ext_rem_len          <= 0;
	     s_tcdm_rem_len         <= 0;
	     s_mchan_ext_add        <= 0;
	     s_mchan_ext_base_add   <= 0;
	     s_mchan_tcdm_add       <= 0;
	     s_mchan_tcdm_base_add  <= 0;
	     s_mchan_ext_count      <= 0;
	     s_mchan_ext_stride     <= 0;
	     s_mchan_tcdm_count     <= 0;
	     s_mchan_tcdm_stride    <= 0;
	  end
	else
	  begin
	     if ( mchan_req_i == 1 && mchan_gnt_o == 1 )
	       begin
		  
		  // EXT ADD COMPUTATION
		  s_mchan_ext_add       <= mchan_ext_add_i;
		  s_mchan_ext_base_add  <= mchan_ext_add_i;
		  
		  s_mchan_tcdm_add      <= mchan_tcdm_add_i;
		  s_mchan_tcdm_base_add <= mchan_tcdm_add_i;
		  
		  // EXT STRIDE AND COUNT COMPUTATION
		  if ( mchan_twd_ext_i == 1)
		    begin
		       s_mchan_ext_count    <= mchan_ext_count_i + 1;
		       s_mchan_ext_stride   <= mchan_ext_stride_i + 1;
		    end
		  else
		    begin
		       s_mchan_ext_count    <= mchan_len_i + 1;
		       s_mchan_ext_stride   <= 0;
		    end
		  
		  // TCDM STRIDE AND COUNT COMPUTATION
		  if ( mchan_twd_tcdm_i == 1)
		    begin
		       s_mchan_tcdm_count   <= mchan_tcdm_count_i + 1;
		       s_mchan_tcdm_stride  <= mchan_tcdm_stride_i + 1;
		    end
		  else
		    begin
		       s_mchan_tcdm_count   <= mchan_len_i + 1;
		       s_mchan_tcdm_stride  <= 0;
		    end
		  
		  // INITIAL REM LEN COMPUTATION
		  s_mchan_rem_len <= mchan_len_i + 1;
		  
		  if ( ( mchan_tcdm_count_i < mchan_len_i )  &&  ( mchan_twd_tcdm_i == 1 ) )
		    s_tcdm_rem_len      <= mchan_tcdm_count_i + 1;
		  else
		    s_tcdm_rem_len      <= mchan_len_i + 1;
		  
		  if ( ( mchan_ext_count_i <= mchan_len_i ) && ( mchan_twd_ext_i == 1) )
		    s_ext_rem_len       <= mchan_ext_count_i + 1;
		  else
		    s_ext_rem_len       <= mchan_len_i + 1;
		  
	       end
	     else
	       begin
		  if ( mchan_req_o == 1'b1 && mchan_gnt_i == 1'b1 )
		    begin
		       
		       s_mchan_rem_len <= s_mchan_rem_len - s_mchan_cur_len;
		       
		       if ( s_ext_rem_len > s_mchan_cur_len )
			 begin
			    s_ext_rem_len         <= s_ext_rem_len   - s_mchan_cur_len;
			    s_mchan_ext_add       <= s_mchan_ext_add + s_mchan_cur_len;
			 end
		       else
			 begin
			    s_ext_rem_len         <= s_mchan_ext_count;
			    s_mchan_ext_add       <= s_mchan_ext_base_add + s_mchan_ext_stride;
			    s_mchan_ext_base_add  <= s_mchan_ext_base_add + s_mchan_ext_stride;
			 end
		       
		       if ( s_tcdm_rem_len > s_mchan_cur_len )
			 begin
			    s_tcdm_rem_len        <= s_tcdm_rem_len - s_mchan_cur_len;
			    s_mchan_tcdm_add      <= s_mchan_tcdm_add + s_mchan_cur_len;
			 end
		       else
			 begin
			    s_tcdm_rem_len        <= s_mchan_tcdm_count;
			    s_mchan_tcdm_add      <= s_mchan_tcdm_base_add + s_mchan_tcdm_stride;
			    s_mchan_tcdm_base_add <= s_mchan_tcdm_base_add + s_mchan_tcdm_stride;
			 end
		       
		    end
	       end
	  end
     end
   
   always_comb
     begin
	
	// CUR LEN COMPUTATION
	s_ext_len_smaller  =  ( s_ext_rem_len  <= s_tcdm_rem_len ) && ( s_ext_rem_len  <= s_mchan_rem_len );
	s_tcdm_len_smaller =  ( s_tcdm_rem_len <= s_ext_rem_len  ) && ( s_tcdm_rem_len <= s_mchan_rem_len );
	
	if ( s_ext_len_smaller ==  1)
	  s_mchan_cur_len     = s_ext_rem_len;
	else
	  if ( s_tcdm_len_smaller ==  1)
	    s_mchan_cur_len   = s_tcdm_rem_len;
	  else
	    s_mchan_cur_len   = s_mchan_rem_len;
     end
   
   always_comb
     begin
	if ( ( s_mchan_rem_len <= s_mchan_cur_len ) )
	  begin
	     s_trans_complete = 1;
	  end
	else
	  begin
	     s_trans_complete = 0;
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
	       mchan_sid_o      = s_mchan_sid;
	       mchan_inc_o      = s_mchan_inc;
	       mchan_tcdm_add_o = s_mchan_tcdm_add;
	       mchan_ext_add_o  = s_mchan_ext_add;
	       
	       if ( mchan_gnt_i == 1'b1 )
		 begin
		    mchan_req_o = 1'b1;
		    if ( s_trans_complete == 1'b1 || ( ( s_mchan_twd_ext == 1'b0 ) && ( s_mchan_twd_tcdm == 1'b0 ) ) )
		      begin
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

   assign mchan_len_o = s_mchan_cur_len - 1;
   
endmodule
