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

module synch_unit
  #(
    // OVERRIDDEN FROM TOP
    parameter NB_CORES           = 1,
    parameter TRANS_SID          = 1,
    parameter TRANS_SID_WIDTH    = 1,
    parameter TRANS_CID_WIDTH    = 1,
    parameter CORE_SID_WIDTH     = 1,
    parameter EXT_ADD_WIDTH      = 29,
    parameter MCHAN_BURST_LENGTH = 64,
    parameter TWD_COUNT_WIDTH    = 16,
    parameter TWD_STRIDE_WIDTH   = 16,
    parameter TWD_QUEUE_WIDTH    = TWD_COUNT_WIDTH+TWD_STRIDE_WIDTH,
    // DEFINED IN MCHAN_DEFINES
    parameter MCHAN_LEN_WIDTH    = `MCHAN_LEN_WIDTH
    )
   (
    
    input  logic                                      clk_i,
    input  logic                                      rst_ni,
    
    // REQUEST INTERFACE
    input  logic                                      cmd_req_i,
    input  logic                                      cmd_gnt_i,
    input  logic [TRANS_SID_WIDTH-1:0]                cmd_sid_i,
    input  logic [MCHAN_LEN_WIDTH-1:0]                cmd_len_i,
    input  logic                                      cmd_twd_i,
    
    input  logic [NB_CORES:0]	                      twd_req_i,
    input  logic [NB_CORES:0][TWD_QUEUE_WIDTH-1:0]    twd_dat_i,
    input  logic [NB_CORES:0][TRANS_SID_WIDTH-1:0]    twd_sid_i,
    
    input  logic [EXT_ADD_WIDTH-1:0]                  ext_add_i,
    
    // RELEASE INTERFACE
    input  logic                                      ext_tx_synch_req_i,
    input  logic [TRANS_SID_WIDTH-1:0]                ext_tx_synch_sid_i,
    
    input  logic                                      ext_rx_synch_req_i,
    input  logic [TRANS_SID_WIDTH-1:0]                ext_rx_synch_sid_i,
    
    input  logic                                      tcdm_tx_synch_req_i,
    input  logic [TRANS_SID_WIDTH-1:0]                tcdm_tx_synch_sid_i,
    
    input  logic                                      tcdm_rx_synch_req_i,
    input  logic [TRANS_SID_WIDTH-1:0]                tcdm_rx_synch_sid_i,
    
    // SYNCHRONIZATION CONTOL
    output logic                                      trans_status_o,
    
    // TERMINATION EVENT
    output logic                                      term_sig_o
    );
   
   logic [TWD_COUNT_WIDTH-1:0] 			      s_twd_count;
   logic [TWD_STRIDE_WIDTH-1:0] 		      s_twd_stride;
   
   logic [MCHAN_LEN_WIDTH-1:0] 			      s_cmd_nb, s_tcdm_cmd_nb, s_ext_cmd_nb;
   logic 					      s_cmd_req, s_tcdm_tx_synch_req, s_tcdm_rx_synch_req, s_ext_tx_synch_req, s_ext_rx_synch_req;
   logic 					      s_pending_transfer,s_pending_transfer_reg;
   logic 					      s_trans_status, s_trans_status_reg;
   
   logic [MCHAN_LEN_WIDTH+4-1:0] 		      s_trans_cells_nb;
   
   integer 					      s_loop1;
   
   always_comb
     begin
	
	s_twd_count  = 0;
	s_twd_stride = 0;
	
	for ( s_loop1 = 0; s_loop1 < NB_CORES + 1; s_loop1++ )
	  begin
	     if ( ( twd_req_i[s_loop1] == 1'b1  ) && ( twd_sid_i[s_loop1] ==  TRANS_SID ) )
	       begin
		  s_twd_count  = twd_dat_i[s_loop1][TWD_COUNT_WIDTH-1:0];
		  s_twd_stride = twd_dat_i[s_loop1][TWD_STRIDE_WIDTH+TWD_COUNT_WIDTH-1:TWD_COUNT_WIDTH];
	       end
	  end
     end
   
   //**********************************************************
   //*** CMD COUNTER ******************************************
   //**********************************************************
   
   cmd_counter
     #(
       .MCHAN_LEN_WIDTH(MCHAN_LEN_WIDTH),
       .TWD_COUNT_WIDTH(TWD_COUNT_WIDTH),
       .TWD_STRIDE_WIDTH(TWD_STRIDE_WIDTH),
       .EXT_ADD_WIDTH(EXT_ADD_WIDTH),
       .MCHAN_BURST_LENGTH(MCHAN_BURST_LENGTH)
       )
   cmd_counter_i
     (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .cmd_req_i(cmd_req_i && cmd_gnt_i && (cmd_sid_i == TRANS_SID) ),
      .cmd_len_i(cmd_len_i),
      .cmd_twd_i(cmd_twd_i),
      .cmd_count_i(s_twd_count),
      .cmd_stride_i(s_twd_stride),
      
      .ext_add_i(ext_add_i),
      
      .cmd_req_o(s_cmd_req),
      .cmd_nb_o(s_cmd_nb)
      );
   
   //**********************************************************
   //*** SIGNALS TO HANDLE CMD AND TX/RX SYNCH REQUESTS *******
   //**********************************************************
   
   assign s_tcdm_tx_synch_req = ( ( tcdm_tx_synch_req_i == 1'b1 ) && ( tcdm_tx_synch_sid_i == TRANS_SID ) );
   assign s_tcdm_rx_synch_req = ( ( tcdm_rx_synch_req_i == 1'b1 ) && ( tcdm_rx_synch_sid_i == TRANS_SID ) );
   assign s_ext_tx_synch_req  = ( ( ext_tx_synch_req_i  == 1'b1 ) && ( ext_tx_synch_sid_i  == TRANS_SID ) );
   assign s_ext_rx_synch_req  = ( ( ext_rx_synch_req_i  == 1'b1 ) && ( ext_rx_synch_sid_i  == TRANS_SID ) );
   
   //**********************************************************
   //*** COMPUTES THE NUMBER OF TCDM OUTSTANDING COMMANDS *****
   //**********************************************************
   
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
	
	if (rst_ni == 1'b0)
	  
	  begin
	     s_tcdm_cmd_nb <= 10'b0;
	  end
	
	else
	  
	  begin
	     
	     case({s_cmd_req,s_tcdm_tx_synch_req,s_tcdm_rx_synch_req})
	       
	       3'b000 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb;
		 end
	       
	       3'b001 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb - 1;
		 end
	       
	       3'b010 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb - 1;
		 end
	       
	       3'b011 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb - 2;
		 end
	       
	       3'b100 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + s_cmd_nb;
		 end
	       
	       3'b101 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + s_cmd_nb - 1;
		 end
	       
	       3'b110 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + s_cmd_nb - 1;
		 end
	       
	       3'b111 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + s_cmd_nb - 2;
		 end
	       
	     endcase
	     
	  end
     end
   
   //**********************************************************
   //** COMPUTES THE NUMBER OF EXT OUTSTANDING COMMANDS *******
   //**********************************************************
   
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
	
	if (rst_ni == 1'b0)
	  
	  begin
	     s_ext_cmd_nb <= 10'b0;
	  end
	
	else
	  
	  begin
	     
	     case({s_cmd_req,s_ext_tx_synch_req,s_ext_rx_synch_req})
	       
	       3'b000 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb;
		 end
	       
	       3'b001 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb - 1;
		 end
	       
	       3'b010 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb - 1;
		 end
	       
	       3'b011 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb - 2;
		 end
	       
	       3'b100 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + s_cmd_nb;
		 end
	       
	       3'b101 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + s_cmd_nb - 1;
		 end
	       
	       3'b110 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + s_cmd_nb - 1;
		 end
	       
	       3'b111 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + s_cmd_nb - 2;
		 end
	       
	     endcase
	     
	  end
     end
   
   //**********************************************************
   //*** COMPUTES THE NUMBER OF OUTSTANDING CELLS *************
   //**********************************************************
   
   always_comb
     begin
	if ( s_ext_cmd_nb > s_tcdm_cmd_nb )
	  s_trans_cells_nb = {s_ext_cmd_nb,4'b0};
	else
	  s_trans_cells_nb = {s_tcdm_cmd_nb,4'b0};
     end
   
   //**********************************************************
   //*** GENERATE AN EVENT WHEN THE TRANSFER IS COMPLETE ******
   //**********************************************************
   
   always_comb 
     begin
	if ( s_trans_cells_nb == 14'b0 )
	  s_pending_transfer = 1'b0;
	else
	  s_pending_transfer = 1'b1;
     end
   
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
	if (rst_ni == 1'b0)
	  s_pending_transfer_reg <= 1'b0;
	else
	  s_pending_transfer_reg <= s_pending_transfer;
     end
   
   always_comb
     begin
	if ( ( s_pending_transfer == 1'b0 ) && ( s_pending_transfer_reg == 1'b1 ) )
	  term_sig_o = 1'b1;
	else
	  term_sig_o = 1'b0;
     end
   
   //**********************************************************
   //*** GENERATE AN EVENT WHEN THE TRANSFER IS COMPLETE ******
   //**********************************************************
   
   always_comb
     begin
	if ( ( s_ext_cmd_nb == 0 ) && ( s_tcdm_cmd_nb == 0 ) )
	  s_trans_status = 1'b0;
	else
	  s_trans_status = 1'b1;
     end
     
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
	if (rst_ni == 1'b0)
	  s_trans_status_reg <= 1'b0;
	else
	  s_trans_status_reg <= s_trans_status;
     end

   always_comb
     begin
	if ( s_trans_status == 1'b1 || s_trans_status_reg == 1'b1 )
	  trans_status_o = 1'b1;
	else
	  trans_status_o = 1'b0;
     end
   
endmodule
