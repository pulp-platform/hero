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

module tcdm_rx_if
  #(
    parameter TRANS_SID_WIDTH = 2,
    parameter TCDM_ADD_WIDTH  = 12
    )
  (
   
   input  logic                        clk_i,
   input  logic                        rst_ni,
   
   // CMD LD INTERFACE
   //***************************************
   input  logic                        beat_eop_i,
   input  logic [TRANS_SID_WIDTH-1:0]  beat_sid_i,
   input  logic [TCDM_ADD_WIDTH-1:0]   beat_add_i,
   input  logic                        beat_we_ni,
   input  logic                        beat_req_i,
   output logic                        beat_gnt_o,
   
   // OUT SYNCHRONIZATION INTERFACE
   //***************************************
   output logic                        synch_req_o,
   output logic [TRANS_SID_WIDTH-1:0]  synch_sid_o,
   
   // RX DATA INTERFACE
   //***************************************
   input  logic [31:0]                 rx_data_dat_i,
   input  logic [3:0]                  rx_data_strb_i,
   output logic                        rx_data_req_o,
   input  logic                        rx_data_gnt_i,
   
   // EXTERNAL INITIATOR
   //***************************************
   output logic                        tcdm_req_o,
   output logic [31:0]                 tcdm_add_o,
   output logic                        tcdm_we_o,
   output logic [31:0]                 tcdm_wdata_o,
   output logic [3:0]                  tcdm_be_o,
   input  logic                        tcdm_gnt_i,
   
   input  logic [31:0]                 tcdm_r_rdata_i,
   input  logic	                       tcdm_r_valid_i
   
   );
   
   //**********************************************************
   //*************** REQUEST CHANNEL **************************
   //**********************************************************
   
   // COMPUTE NEXT STATE
   always_comb
     begin
	
	rx_data_req_o    = '0;
	tcdm_req_o       = '0;
	beat_gnt_o       = '0;
	synch_req_o      = '0;
	synch_sid_o      = '0;
	
	begin
	   if ( beat_req_i == 1'b1 && beat_we_ni == 1'b0  && rx_data_gnt_i == 1'b1 ) // RX OPERATION && REQUEST FROM COMMAND QUEUE && RX BUFFER AVAILABLE
	     begin
		tcdm_req_o = 1'b1;
		if ( tcdm_gnt_i == 1'b1 ) // THE TRANSACTION IS GRANTED FROM THE TCDM
		  begin
		     synch_req_o   = beat_eop_i;
		     synch_sid_o   = beat_sid_i;
		     beat_gnt_o    = 1'b1;
		     rx_data_req_o = 1'b1;
		  end
	     end
	end
     end
   
   //**********************************************************
   //********** BINDING OF INPUT/OUTPUT SIGNALS ***************
   //**********************************************************
   
   assign tcdm_add_o   = 32'd0 | beat_add_i;
   assign tcdm_be_o    = rx_data_strb_i;
   assign tcdm_we_o    = beat_we_ni;
   assign tcdm_wdata_o = rx_data_dat_i;
   
endmodule
