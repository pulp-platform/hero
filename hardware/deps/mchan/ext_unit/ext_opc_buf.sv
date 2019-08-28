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

module ext_opc_buf
  #(
    parameter TRANS_SID_WIDTH = 2,
    parameter TCDM_ADD_WIDTH  = 12,
    parameter TCDM_OPC_WIDTH  = 12,
    parameter EXT_TID_WIDTH   = 4,
    parameter MCHAN_LEN_WIDTH = 15
    )
   (
    
    input  logic                       clk_i,
    input  logic		       rst_ni,
    
    /// WRITE PORT
    input  logic                       tid_valid_i,
    input  logic [EXT_TID_WIDTH-1:0]   tid_i,
    input  logic [TCDM_OPC_WIDTH-1:0]  opc_i,
    input  logic [MCHAN_LEN_WIDTH-1:0] len_i,
    input  logic [TCDM_ADD_WIDTH-1:0]  r_add_i,
    input  logic [2:0]                 add_i,
    input  logic [TRANS_SID_WIDTH-1:0] sid_i,
    
    // READ PORT
    input  logic [EXT_TID_WIDTH-1:0]   r_tid_i,
    output logic [TCDM_OPC_WIDTH-1:0]  tcdm_opc_o,
    output logic [MCHAN_LEN_WIDTH-1:0] tcdm_len_o,
    output logic [TCDM_ADD_WIDTH-1:0]  tcdm_add_o,
    output logic [TRANS_SID_WIDTH-1:0] tcdm_sid_o,
    
    output logic [2:0]                 trans_rx_ext_add_o,
    output logic [2:0]                 trans_rx_tcdm_add_o,
    output logic [MCHAN_LEN_WIDTH-1:0] trans_rx_len_o,
    
    output logic [TRANS_SID_WIDTH-1:0] synch_sid_o
    
    );
   
   localparam OPC_BUF_WIDTH = TCDM_OPC_WIDTH+MCHAN_LEN_WIDTH+3+TCDM_ADD_WIDTH+TRANS_SID_WIDTH;
   localparam OPC_BUF_DEPTH = 2**EXT_TID_WIDTH;
   
   logic [OPC_BUF_WIDTH-1:0] 	       mem[OPC_BUF_DEPTH-1:0];
   logic [TCDM_OPC_WIDTH-1:0] 	       s_opc;
   
   integer 			       i;
   
   // WRITE PORT
   always_ff @ (posedge clk_i, negedge rst_ni)
     begin
        if(rst_ni == 1'b0)
          begin
	     for(i=0;i<OPC_BUF_DEPTH;i++)
	       mem[i] <= '0;
          end
        else
          begin
	     if(tid_valid_i == 1'b1)
	       mem[tid_i] <= {opc_i,len_i,add_i,r_add_i,sid_i};
          end
     end
   
   // READ PORT
   always_comb
     begin
	{s_opc,tcdm_len_o,trans_rx_ext_add_o,tcdm_add_o,tcdm_sid_o} = mem[r_tid_i];
     end
   
   // EXCHANGE LOAD/STORE OPS IN TCDM CMD QUEUE
   always_comb
     begin
	
	tcdm_opc_o = s_opc;
	
	if ( s_opc[0] == 1'b1 )
	  tcdm_opc_o[0] = 1'b0;
	else
	  if ( s_opc[0] == 1'b0 )
	    tcdm_opc_o[0] = 1'b1;
	  else
	    tcdm_opc_o[0] = 1'b0;
	
     end
   
   assign trans_rx_tcdm_add_o = tcdm_add_o[2:0];
   assign trans_rx_len_o      = tcdm_len_o;
     
   assign synch_sid_o         = tcdm_sid_o;
   
endmodule
