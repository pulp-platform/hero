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

module trans_arbiter_wrap
  #(
    parameter DATA_WIDTH          = 32,
    parameter NB_CORES            = 2,
    parameter MCHAN_LEN_WIDTH     = 5,
    parameter TCDM_ADD_WIDTH      = 16,
    parameter EXT_ADD_WIDTH       = 32,
    parameter MCHAN_OPC_WIDTH     = 1,
    parameter TWD_QUEUE_ADD_WIDTH = 1,
    parameter TRANS_SID_WIDTH     = 1,
    parameter TRANS_CID_WIDTH     = 1
    )
   (
    input  logic                                       clk_i,
    input  logic                                       rst_ni,
    
    // ---------------- REQ_SIDE --------------------------
    input  logic [NB_CORES:0]                          req_i,
    output logic [NB_CORES:0]                          gnt_o,
    input  logic [NB_CORES:0][EXT_ADD_WIDTH-1:0]       ext_add_i,
    input  logic [NB_CORES:0][TCDM_ADD_WIDTH-1:0]      tcdm_add_i,
    input  logic [NB_CORES:0][MCHAN_LEN_WIDTH-1:0]     len_i,
    input  logic [NB_CORES:0][MCHAN_OPC_WIDTH-1:0]     opc_i,
    input  logic [NB_CORES:0]                          inc_i,
    input  logic [NB_CORES:0]                          twd_i,
    input  logic [NB_CORES:0]                          ele_i,
    input  logic [NB_CORES:0]                          ile_i,
    input  logic [NB_CORES:0]                          ble_i,
    input  logic [NB_CORES:0][TWD_QUEUE_ADD_WIDTH-1:0] twd_add_i,
    input  logic [NB_CORES:0][TRANS_SID_WIDTH-1:0]     sid_i,
    
    // Outputs
    output logic                                       req_o,
    input  logic                                       gnt_i,
    output logic [EXT_ADD_WIDTH-1:0]                   ext_add_o,
    output logic [TCDM_ADD_WIDTH-1:0]                  tcdm_add_o,
    output logic [MCHAN_LEN_WIDTH-1:0]                 len_o,
    output logic [MCHAN_OPC_WIDTH-1:0]                 opc_o,
    output logic                                       inc_o,
    output logic                                       twd_o,
    output logic                                       ele_o,
    output logic                                       ile_o,
    output logic                                       ble_o,
    output logic [TWD_QUEUE_ADD_WIDTH-1:0]             twd_add_o,
    output logic [TRANS_SID_WIDTH-1:0]                 sid_o,
    
    output logic [TRANS_CID_WIDTH-1:0]                 cid_o
    );
   
   logic [(2**($clog2(NB_CORES)+1))-1:0][DATA_WIDTH-1:0] s_dat;
   logic [(2**($clog2(NB_CORES)+1))-1:0] 		 s_req;
   logic [(2**($clog2(NB_CORES)+1))-1:0] 		 s_gnt;
   genvar 						 i;
   
   // CORES
   generate
      for (i =0; i<NB_CORES+1; i++)
	begin
	   assign s_dat[i] = {sid_i[i],twd_add_i[i],ble_i[i],ile_i[i],ele_i[i],twd_i[i],inc_i[i],opc_i[i],len_i[i],tcdm_add_i[i],ext_add_i[i]};
	   assign s_req[i] = req_i[i];
	   assign gnt_o[i] = s_gnt[i];
	end
   endgenerate
   
   generate
      for (i =NB_CORES+1; i<2**($clog2(NB_CORES)+1); i++)
	begin
	   assign s_dat[i] = '0;
	   assign s_req[i] = '0;
	end
   endgenerate
   
   mchan_arbiter
     #(
       .DATA_WIDTH(DATA_WIDTH),
       .N_MASTER(2**($clog2(NB_CORES)+1)),
       .LOG_MASTER(TRANS_CID_WIDTH)
       )
   arbiter_i
     (
      
      .clk     ( clk_i  ),
      .rst_n   ( rst_ni ),
      
      .data_i  ( s_dat  ),
      .req_i   ( s_req  ),
      .gnt_o   ( s_gnt  ),
      
      .req_o   ( req_o  ),
      .gnt_i   ( gnt_i  ),
      .id_o    ( cid_o  ),
      .data_o  ( {sid_o,twd_add_o,ble_o,ile_o,ele_o,twd_o,inc_o,opc_o,len_o,tcdm_add_o,ext_add_o} )
      
      );
   
endmodule
