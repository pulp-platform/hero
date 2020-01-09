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
    parameter NB_CTRLS           = 1,
    parameter TRANS_SID          = 1,
    parameter TRANS_SID_WIDTH    = 1,
    parameter EXT_ADD_WIDTH      = 29,
    parameter TCDM_ADD_WIDTH     = 29,
    parameter MCHAN_BURST_LENGTH = 64,
    parameter TWD_COUNT_WIDTH    = 16,
    parameter TWD_STRIDE_WIDTH   = 16,
    // DEFINED IN MCHAN_DEFINES
    parameter MCHAN_LEN_WIDTH    = `MCHAN_LEN_WIDTH,
    // DERIVED
    parameter TWD_QUEUE_WIDTH    = TWD_COUNT_WIDTH+TWD_STRIDE_WIDTH,
    parameter MCHAN_CMD_WIDTH    = MCHAN_LEN_WIDTH - $clog2(MCHAN_BURST_LENGTH) + 1
    )
   (
    
    input logic 		      clk_i,
    input logic 		      rst_ni,
    
    // REQUEST INTERFACE
    input logic 		      mchan_tx_req_i,
    input logic 		      mchan_tx_gnt_i,
    input logic [TRANS_SID_WIDTH-1:0] mchan_tx_sid_i,
    input logic [MCHAN_CMD_WIDTH-1:0] mchan_tx_cmd_nb_i,
    
    input logic 		      mchan_rx_req_i,
    input logic 		      mchan_rx_gnt_i,
    input logic [TRANS_SID_WIDTH-1:0] mchan_rx_sid_i,
    input logic [MCHAN_CMD_WIDTH-1:0] mchan_rx_cmd_nb_i,
    
    // RELEASE INTERFACE
    input logic 		      ext_tx_synch_req_i,
    input logic [TRANS_SID_WIDTH-1:0] ext_tx_synch_sid_i,
    
    input logic 		      ext_rx_synch_req_i,
    input logic [TRANS_SID_WIDTH-1:0] ext_rx_synch_sid_i,
    
    input logic 		      tcdm_tx_synch_req_i,
    input logic [TRANS_SID_WIDTH-1:0] tcdm_tx_synch_sid_i,
    
    input logic 		      tcdm_rx_synch_req_i,
    input logic [TRANS_SID_WIDTH-1:0] tcdm_rx_synch_sid_i,
    
    // SYNCHRONIZATION CONTOL
    output logic 		      trans_status_o,
    
    // TERMINATION EVENT
    output logic 		      term_sig_o
    );
      
   logic [MCHAN_CMD_WIDTH-1:0] 			    s_tcdm_cmd_nb, s_ext_cmd_nb;
   logic 					    s_cmd_req, s_tcdm_tx_synch_req, s_tcdm_rx_synch_req, s_ext_tx_synch_req, s_ext_rx_synch_req;
   logic 					    s_pending_transfer,s_pending_transfer_reg;
   logic 					    s_trans_status, s_trans_status_reg;
   
   logic [MCHAN_CMD_WIDTH+4-1:0] 		    s_trans_cells_nb;
   logic 					    s_mchan_rx_req,s_mchan_tx_req;
   
   always_comb
     begin
	if ( ( mchan_rx_req_i && mchan_rx_gnt_i && (mchan_rx_sid_i == TRANS_SID) ) )
	  s_mchan_rx_req = 1'b1;
	else
	  s_mchan_rx_req = 1'b0;
     end
   
   always_comb
     begin
	if ( ( mchan_tx_req_i && mchan_tx_gnt_i && (mchan_tx_sid_i == TRANS_SID) ) )
	  s_mchan_tx_req = 1'b1;
	else
	  s_mchan_tx_req = 1'b0;
     end
   
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
	     
	     case({s_mchan_tx_req,s_mchan_rx_req,s_tcdm_tx_synch_req,s_tcdm_rx_synch_req})
	       
	       4'b0000 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb;
		 end
	       
	       4'b0001 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb - 1;
		 end
	       
	       4'b0010 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb - 1;
		 end
	       
	       4'b0011 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb - 2;
		 end
	       
	       4'b0100 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + mchan_rx_cmd_nb_i;
		 end
	       
	       4'b0101 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + mchan_rx_cmd_nb_i - 1;
		 end
	       
	       4'b0110 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + mchan_rx_cmd_nb_i - 1;
		 end
	       
	       4'b0111 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + mchan_rx_cmd_nb_i - 2;
		 end
	       
	       4'b1000 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + mchan_tx_cmd_nb_i;
		 end
	       
	       4'b1001 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + mchan_tx_cmd_nb_i - 1;
		 end
	       
	       4'b1010 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + mchan_tx_cmd_nb_i - 1;
		 end
	       
	       4'b1011 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + mchan_tx_cmd_nb_i - 2;
		 end
	       
	       4'b1100 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + mchan_rx_cmd_nb_i + mchan_tx_cmd_nb_i;
		 end
	       
	       4'b1101 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + mchan_rx_cmd_nb_i + mchan_tx_cmd_nb_i - 1;
		 end
	       
	       4'b1110 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + mchan_rx_cmd_nb_i + mchan_tx_cmd_nb_i - 1;
		 end
	       
	       4'b1111 :
		 begin
		    s_tcdm_cmd_nb <= s_tcdm_cmd_nb + mchan_rx_cmd_nb_i + mchan_tx_cmd_nb_i - 2;
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
	     
	     case({s_mchan_tx_req,s_mchan_rx_req,s_ext_tx_synch_req,s_ext_rx_synch_req})
	       
	       4'b0000 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb;
		 end
	       
	       4'b0001 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb - 1;
		 end
	       
	       4'b0010 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb - 1;
		 end
	       
	       4'b0011 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb - 2;
		 end
	       
	       4'b0100 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + mchan_rx_cmd_nb_i;
		 end
	       
	       4'b0101 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + mchan_rx_cmd_nb_i - 1;
		 end
	       
	       4'b0110 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + mchan_rx_cmd_nb_i - 1;
		 end
	       
	       4'b0111 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + mchan_rx_cmd_nb_i - 2;
		 end
	       
	       4'b1000 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + mchan_tx_cmd_nb_i;
		 end
	       
	       4'b1001 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + mchan_tx_cmd_nb_i - 1;
		 end
	       
	       4'b1010 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + mchan_tx_cmd_nb_i - 1;
		 end
	       
	       4'b1011 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + mchan_tx_cmd_nb_i - 2;
		 end
	       
	       4'b1100 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + mchan_rx_cmd_nb_i + mchan_tx_cmd_nb_i;
		 end
	       
	       4'b1101 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + mchan_rx_cmd_nb_i + mchan_tx_cmd_nb_i - 1;
		 end
	       
	       4'b1110 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + mchan_rx_cmd_nb_i + mchan_tx_cmd_nb_i - 1;
		 end
	       
	       4'b1111 :
		 begin
		    s_ext_cmd_nb <= s_ext_cmd_nb + mchan_rx_cmd_nb_i + mchan_tx_cmd_nb_i - 2;
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
   
   //***********************************************************
   //*** GENERATES AN EVENT WHEN THE TRANSFER IS COMPLETE ******
   //***********************************************************
   
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
