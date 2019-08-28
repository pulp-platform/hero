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

module tcdm_tx_if
#(
    parameter TRANS_SID_WIDTH = 2,
    parameter TCDM_ADD_WIDTH  = 12,
    parameter DEBUG = 0
)
(
   
    input  logic                       clk_i,
    input  logic                       rst_ni,
    
    // CMD LD INTERFACE
    //***************************************
    input  logic                       beat_eop_i,
    input  logic [TRANS_SID_WIDTH-1:0] beat_sid_i,
    input  logic [TCDM_ADD_WIDTH-1:0]  beat_add_i,
    input  logic                       beat_we_ni,
    input  logic                       beat_req_i,
    output logic                       beat_gnt_o,
    
    // OUT SYNCHRONIZATION INTERFACE
    //***************************************
    output logic                       synch_req_o,
    output logic [TRANS_SID_WIDTH-1:0] synch_sid_o,
    
    // WRITE DATA INTERFACE
    //***************************************
    output logic [31:0]                tx_data_dat_o,
    output logic                       tx_data_req_o,
    input  logic                       tx_data_gnt_i,
    
    // EXTERNAL INITIATOR
    //***************************************
    output logic                       tcdm_req_o,
    output logic [31:0]                tcdm_add_o,
    output logic                       tcdm_we_o,
    output logic [31:0]                tcdm_wdata_o,
    output logic [3:0]                 tcdm_be_o,
    input  logic                       tcdm_gnt_i,
    
    input  logic [31:0]                tcdm_r_rdata_i,
    input  logic                       tcdm_r_valid_i

);
   
   logic [31:0]                        s_tcdm_r_rdata;
   logic [TRANS_SID_WIDTH-1:0]         s_beat_sid;
   logic                               s_beat_eop;
   logic                               s_push_req,s_pop_req;
   logic                               s_trans_stalled;
   logic                               s_sample_tx_data, s_forward_tx_data;
   
   // FSM STATES SIGNALS
   enum              `ifdef SYNTHESIS logic [1:0] `endif { TRANS_RUN, TRANS_STALLED } CS, NS;
   
   // SAMPLES tcdm_r_rdata WHEN A STALL CONDITION OCCOURS
   always_ff @ (posedge clk_i, negedge rst_ni)
   begin
         if (rst_ni == 1'b0)
         begin
               s_tcdm_r_rdata <= '0;
         end
         else
         begin
               if ( s_sample_tx_data == 1'b1 )
               begin
                  s_tcdm_r_rdata <= tcdm_r_rdata_i;
               end
         end
   end
   
   // MUXES THE COMBINATIONAL AND SYNCHRONOUS VESRION OF tcdm_r_rdata
   always_comb
   begin
         if ( s_forward_tx_data == 1'b1 )
         begin
            tx_data_dat_o  = s_tcdm_r_rdata;
         end
         else
         begin
            tx_data_dat_o  = tcdm_r_rdata_i;
         end
   end
   
   //**********************************************************
   //*************** REQUEST CHANNEL **************************
   //**********************************************************
   
   // COMPUTE NEXT STATE
   always_comb
   begin
  
      tcdm_req_o       = '0;
      beat_gnt_o       = '0;
      s_push_req       = '0;
  
      if ( beat_req_i == 1'b1 && beat_we_ni == 1'b1 && s_trans_stalled == 1'b0 ) // REQUEST FROM COMMAND QUEUE && RX OPERATION && TX BUFFER AVAILABLE
      begin
            tcdm_req_o = 1'b1;
             if ( tcdm_gnt_i == 1'b1 ) // THE TRANSACTION IS GRANTED FROM THE TCDM
             begin
                  beat_gnt_o  = 1'b1;
                  s_push_req  = 1'b1;
             end
      end

   end
   
    //**********************************************************
    //********** DECOUPLE REQUEST AND RESPONE CHANNEL **********
    //**********************************************************
   //synopsys translate_off
   if (DEBUG) begin
      initial begin
         $display("%s[MCHAN - TCDM_UNIT] %s%t - %s%m tcdm_tx_cmd_queue_i.DATA_WIDTH = %d%s", "\x1B[1;34m", "\x1B[0;37m", $time, "\x1B[0;35m", TRANS_SID_WIDTH+1, "\x1B[0m");
         $display("%s[MCHAN - TCDM_UNIT] %s%t - %s%m tcdm_tx_cmd_queue_i.DATA_DEPTH = %d%s", "\x1B[1;34m", "\x1B[0;37m", $time, "\x1B[0;35m", 2, "\x1B[0m");
      end
   end
   //synopsys translate_on 

    mchan_fifo
    #(
      .DATA_WIDTH    ( TRANS_SID_WIDTH+1         ),
      .DATA_DEPTH    ( 2                         )
    )
    tcdm_tx_cmd_queue_i
    (
        .clk_i       ( clk_i                    ),
        .rst_ni      ( rst_ni                   ),

        .push_dat_i  ( {beat_sid_i,beat_eop_i}  ),
        .push_req_i  ( s_push_req               ),
        .push_gnt_o  (                          ),

        .pop_dat_o   ( {s_beat_sid,s_beat_eop}  ),
        .pop_req_i   ( s_pop_req                ),
        .pop_gnt_o   (                          )
    );

   //**********************************************************
   //*************** RESPONSE CHANNEL *************************
   //**********************************************************
   
   // UPDATE THE STATE
   always_ff @(posedge clk_i, negedge  rst_ni)
     begin : UPDATE_STATE
  if(rst_ni == 1'b0)
    CS <= TRANS_RUN;
  else
    CS <= NS;
     end
   
   // COMPUTE NEXT STATE
   always_comb
     begin : COMPUTE_STATE
  
  tx_data_req_o     = '0;
  synch_req_o       = '0;
  synch_sid_o       = '0;
  s_pop_req         = '0;
  s_sample_tx_data  = '0;
  s_forward_tx_data = '0;
  s_trans_stalled   = '0;
  
  case(CS)
    
    TRANS_RUN:
      begin
         s_sample_tx_data  = 1'b1;
         if ( tcdm_r_valid_i == 1'b1 )
     begin
        if ( tx_data_gnt_i == 1'b1 )
          begin
       s_pop_req = 1'b1;
       tx_data_req_o = 1'b1;
       NS = TRANS_RUN;
       if ( s_beat_eop == 1'b1)
         begin
            synch_req_o = 1'b1;
            synch_sid_o = s_beat_sid;
         end
          end
        else
          begin
       s_trans_stalled = 1'b1;
       NS              = TRANS_STALLED;
          end
     end
         else
     begin
        NS = TRANS_RUN;
     end
      end
    
    TRANS_STALLED:
      begin
         s_forward_tx_data = 1'b1;
         s_trans_stalled   = 1'b1;
         if ( tx_data_gnt_i == 1'b1 )
     begin
        s_pop_req = 1'b1;
        tx_data_req_o = 1'b1;
        NS = TRANS_RUN;
        if ( s_beat_eop == 1'b1)
          begin
       synch_req_o = 1'b1;
       synch_sid_o = s_beat_sid;
          end
     end
         else
     begin
        NS = TRANS_STALLED;
     end
      end
    
    default:
      NS = TRANS_RUN;
    
  endcase
  
     end
   
   //**********************************************************
   //********** BINDING OF INPUT/OUTPUT SIGNALS ***************
   //**********************************************************
   
   assign tcdm_add_o   = 32'd0 | beat_add_i;
   assign tcdm_be_o    = 4'b1111;
   assign tcdm_we_o    = beat_we_ni;
   assign tcdm_wdata_o = '0;
   
endmodule
