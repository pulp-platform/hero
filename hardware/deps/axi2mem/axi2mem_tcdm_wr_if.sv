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

module axi2mem_tcdm_wr_if
(
   input  logic        clk_i,
   input  logic        rst_ni,

   // CMD LD INTERFACE
   //***************************************
   input  logic [5:0]  trans_id_i,
   input  logic [31:0] trans_add_i,
   input  logic        trans_last_i,
   input  logic        trans_req_i,
   output logic        trans_gnt_o,

   // OUT SYNCHRONIZATION INTERFACE
   //***************************************
   output logic        synch_req_o,
   output logic [5:0]  synch_id_o,

   // RX DATA INTERFACE
   //***************************************
   input  logic [31:0] data_dat_i,
   input  logic [3:0]  data_strb_i,
   output logic        data_req_o,
   input  logic        data_gnt_i,

   // EXTERNAL INITIATOR
   //***************************************
   output logic        tcdm_req_o,
   output logic [31:0] tcdm_add_o,
   output logic        tcdm_we_o,
   output logic [31:0] tcdm_wdata_o,
   output logic [3:0]  tcdm_be_o,
   input  logic        tcdm_gnt_i,

   input  logic [31:0] tcdm_r_rdata_i,
   input  logic        tcdm_r_valid_i
);
   
   //**********************************************************
   //*************** REQUEST CHANNEL **************************
   //**********************************************************
   
   // COMPUTE NEXT STATE
   always_comb
     begin
        
        data_req_o    = '0;
        tcdm_req_o    = '0;
        trans_gnt_o   = '0;
        synch_req_o   = '0;
        synch_id_o    = '0;
        
        begin
           if ( trans_req_i == 1'b1 && data_gnt_i == 1'b1 ) // RX OPERATION && REQUEST FROM COMMAND QUEUE && RX BUFFER AVAILABLE
             begin
                if ( | data_strb_i ) // AT LEAST ONE LANE IS ACTIVATED TO WRITE INTO TCDM
                  begin
                     tcdm_req_o = 1'b1;
                     if ( tcdm_gnt_i == 1'b1 ) // THE TRANSACTION IS GRANTED FROM THE TCDM
                       begin
                          synch_req_o   = trans_last_i;
                          synch_id_o    = trans_id_i;
                          trans_gnt_o   = 1'b1;
                          data_req_o    = 1'b1;
                       end
                  end
                else
                  begin
                     synch_req_o   = trans_last_i;
                     synch_id_o    = trans_id_i;
                     trans_gnt_o   = 1'b1;
                     data_req_o    = 1'b1;
                  end
             end
        end
     end
   
   //**********************************************************
   //********** BINDING OF INPUT/OUTPUT SIGNALS ***************
   //**********************************************************
   
   assign tcdm_add_o   = trans_add_i;
   assign tcdm_be_o    = data_strb_i;
   assign tcdm_we_o    = 1'b0;
   assign tcdm_wdata_o = data_dat_i;
   
endmodule
