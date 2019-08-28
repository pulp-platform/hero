// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Company:        Institute of Integrated Systems // ETH Zurich              //
//                                                                            //
// Engineer:       Roberto Roncone - roncone@iis.ee.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                      Igor Loi                                              //
//                                                                            //
// Create Date:    12/03/2015                                                 //
// Design Name:    event_unit                                                 //
// Module Name:    event_unit_mux                                             //
// Project Name:   PULP                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:                                                               //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (17/03/2015) Improved Identation                           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
`include "old_event_unit_defines.sv"

module event_unit_mux
#(
    parameter NUM_CORES=4
)
(
    // Rst and Clock
    input  logic                clk_i,
    input  logic                rst_ni,
    // Other signals
    input  logic[63:0]          evnt_buffer_clear_i,
    input  logic                barrier_event_i,
    input  logic[`GP_EVNT-1:0]  GP_events_i,
    input  logic[3:0]           tmr_events_i,
    input  logic                dma_events_i,
    input  logic[1:0]           hwce_events_i,
    input  logic[7:0]           ext_events_i,
    input  logic                emergency_event_i,
    input  logic                emergency_event_clear_i,
    output logic                emergency_event_status_o,
    input  logic[1:0]           evnt_mask_sel_i,
    input  logic[63:0]          evnt_mask_i,
    output logic                r_event_detect_o,
    output logic[31:0]          event_buffer_status_low_o, //LSB:GP events,dma,tmr,external,not used:MSB
    output logic[31:0]          event_buffer_status_high_o, //32 bit not used at the moment
    output logic[63:0]          r_mask_o
);

   logic [31:0]                 s_evnt_buffer_clear_high;
   logic [31:0]                 s_evnt_mask_high;
   logic [31:0]                 r_evnt_mask_high;
   logic                        s_evnt_mask_sel_high;
   logic [31:0]                 s_events_high;
   logic [31:0]                 r_events_high;
   logic                        r_event_detected_high;
   logic [31:0]                 edge_detected_high;
   logic [31:0]                 r_events_buff_high;
   logic [31:0]                 r_events_masked_high;


   logic [31:0]                 s_evnt_buffer_clear_low;
   logic [31:0]                 s_evnt_mask_low;
   logic [31:0]                 r_evnt_mask_low;
   logic                        s_evnt_mask_sel_low;
   logic [31:0]                 s_events_low;
   logic [31:0]                 r_events_low;
   logic                        r_event_detected_low;
   logic [31:0]                 edge_detected_low;
   logic [31:0]                 r_events_buff_low;
   logic [31:0]                 r_events_masked_low;

   //EMERGENCY EVENTS
   logic                        s_emergency_event;
   logic                        r_emergency_event;
   logic                        r_emergency_event_buff;
   logic                        emergency_event_detected;
   logic                        emergency_clear;





   genvar               i;


   assign s_evnt_mask_low          = evnt_mask_i[31:0];
   assign s_evnt_mask_high         = evnt_mask_i[63:32];
   assign s_evnt_mask_sel_low      = evnt_mask_sel_i[0];
   assign s_evnt_mask_sel_high     = evnt_mask_sel_i[1];
   assign s_evnt_buffer_clear_low  = evnt_buffer_clear_i[31:0];
   assign s_evnt_buffer_clear_high = evnt_buffer_clear_i[63:32];
   assign r_event_detected_high    = 0;


   assign r_event_detect_o          = r_emergency_event_buff | r_event_detected_low | r_event_detected_high;
   assign event_buffer_status_low_o = { {(12){1'b0}}, r_events_masked_low};

   assign s_events_low = { 12'b0,
                           hwce_events_i,
                           ext_events_i,
                           dma_events_i,
                           tmr_events_i,
                           GP_events_i,
                           barrier_event_i};

   assign event_buffer_status_high_o = { {(32){1'b0}} };
   assign r_mask_o                   = { r_evnt_mask_high,r_evnt_mask_low};
   assign emergency_event_status_o   = r_emergency_event_buff;



   //**********************************************************
   //*************** MASK REGISTER ****************
   //**********************************************************
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if (rst_ni == 1'b0)
          begin
             r_evnt_mask_low <= 'b0;
             r_evnt_mask_high <= 'b0;
          end
        else
          begin
             if( s_evnt_mask_sel_low == 1 )
               begin
                  r_evnt_mask_low <= s_evnt_mask_low;
               end
             if( s_evnt_mask_sel_high == 1 )
               begin
                  r_evnt_mask_high <= s_evnt_mask_high;
               end
          end
     end

   //**********************************************************
   //*************** EMERGENCY EVENT DETECTION,BUFFERING,MASKING ****************
   //**********************************************************
   assign emergency_clear   = emergency_event_clear_i;
   assign s_emergency_event = emergency_event_i;

   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if (rst_ni == 1'b0)
          begin
             r_emergency_event <= 'b0;
          end
        else
          begin
             r_emergency_event <= s_emergency_event;
          end
     end

   assign emergency_event_detected =~(r_emergency_event) & s_emergency_event;


   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if ( (rst_ni) == 1'b0)
          begin
             r_emergency_event_buff <= 1'b0;
          end
        else
          begin
             case ({emergency_clear,emergency_event_detected})
               2'b00:
                 begin
                    r_emergency_event_buff <= r_emergency_event_buff;
                 end

               2'b01:
                 begin
                    r_emergency_event_buff <= s_emergency_event;
                 end

               2'b10:
                 begin
                    r_emergency_event_buff <= 1'b0;
                 end

               2'b11:
                 begin
                    r_emergency_event_buff <= 1'b0;
                 end
             endcase
          end

     end


   //**********************************************************
   //*************** EVENT DETECTION,BUFFERING,MASKING *******
   //**********************************************************

   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if (rst_ni == 1'b0)
          begin
             r_events_low <= 'b0;
          end
        else
          begin
             r_events_low <= s_events_low;
          end
     end

   assign edge_detected_low =~(r_events_low) & s_events_low;

   generate
      for( i=0; i<32; i++)
        begin : events_buff
           always_ff @(posedge clk_i, negedge rst_ni)
             begin
                if ( (rst_ni) == 1'b0)
                  begin
                     r_events_buff_low[i] <= 1'b0;
                  end
                else
                  begin
                     case ({s_evnt_buffer_clear_low[i],edge_detected_low[i]})
                       2'b00:
                         begin
                            r_events_buff_low[i] <= r_events_buff_low[i];
                         end

                       2'b01:
                         begin
                            r_events_buff_low[i] <= s_events_low[i];
                         end

                       2'b10:
                         begin
                            r_events_buff_low[i] <= 1'b0;
                         end

                       2'b11:
                         begin
                            r_events_buff_low[i] <= 1'b0;
                         end

                       default:
                         begin
                            r_events_buff_low[i] <= 1'b0;
                         end
                     endcase
                  end

             end
        end
   endgenerate

   assign r_events_masked_low = r_events_buff_low & r_evnt_mask_low;

   always_comb
     begin
        if( r_events_masked_low != 0 )
          r_event_detected_low = 1;
        else
	  r_event_detected_low = 0;
     end


endmodule
