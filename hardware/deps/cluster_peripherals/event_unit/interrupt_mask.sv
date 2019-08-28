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
//                                                                            //
// Create Date:    12/03/2015                                                 //
// Design Name:    event_unit                                                 //
// Module Name:    Interrupt_mask                                             //
// Project Name:   PULP                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:                                                               //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
`include "old_event_unit_defines.sv"

module interrupt_mask
  #(
    parameter NUM_CORES=4
    )
   (
     input logic               clk_i,
     input logic               rst_ni,
     input logic[63:0]         interrupt_buffer_clear_i,
     input logic               barrier_interrupt_i,
     input logic[`GP_EVNT-1:0] GP_interrupt_i,
     input logic[3:0]          tmr_interrupt_i,
     input logic               dma_interrupt_i,
     input logic[1:0]          hwce_interrupt_i,
     input logic[7:0]          ext_interrupt_i,
     input logic               emergency_interrupt_i,
     input logic               emergency_interrupt_clear_i,
     output logic              emergency_interrupt_status_o,
     input logic[1:0]          interrupt_mask_sel_i,
     input logic[63:0]         interrupt_mask_i,
     output logic              IRQ_o,
     output logic              NMIRQ_o,
     output logic[31:0]        interrupt_buffer_status_low_o,
     output logic[31:0]        interrupt_buffer_status_high_o,
     output logic[63:0]        r_mask_o

     );

   logic [31:0]         s_interrupt_buffer_clear_low;
   logic [31:0]         s_interrupt_buffer_clear_high;
   logic [31:0]         s_interrupt_mask_low;
   logic [31:0]         s_interrupt_mask_high;
   logic [31:0]         r_interrupt_mask_low;
   logic [31:0]         r_interrupt_mask_high;
   logic                s_interrupt_mask_sel_low;
   logic                s_interrupt_mask_sel_high;
   logic                r_interrupt_detected_high;

   logic [31:0]         s_interrupt_low;
   logic [31:0]         r_interrupt_low;
   logic                r_interrupt_detected_low;
   logic [31:0]         r_interrupt_buff_low;
   logic [31:0]         r_interrupt_masked_low;
   logic [31:0]         edge_detected_low;


   //EMERGENCY IRQS
   logic                s_emergency_interrupt;
   logic                r_emergency_interrupt;
   logic                r_emergency_interrupt_buff;
   logic                emergency_interrupt_detected;
   logic                emergency_clear;

   genvar               i;


   assign s_interrupt_mask_low          = interrupt_mask_i[31:0];
   assign s_interrupt_mask_high         = interrupt_mask_i[63:32];
   assign s_interrupt_mask_sel_low      = interrupt_mask_sel_i[0];
   assign s_interrupt_mask_sel_high     = interrupt_mask_sel_i[1];
   assign s_interrupt_buffer_clear_low  = interrupt_buffer_clear_i[31:0];
   assign s_interrupt_buffer_clear_high = interrupt_buffer_clear_i[63:32];



   assign IRQ_o                          = (r_interrupt_detected_low|r_interrupt_detected_high);
   assign NMIRQ_o                        = r_emergency_interrupt_buff;
   assign interrupt_buffer_status_low_o  = { 12'b0, r_interrupt_masked_low};
   assign interrupt_buffer_status_high_o = { 32'b0};
   assign r_mask_o                       = { r_interrupt_mask_high,r_interrupt_mask_low};
   assign emergency_interrupt_status_o   = r_emergency_interrupt_buff;
   assign r_interrupt_detected_high      = 0;

   assign s_interrupt_low = { 12'b0,
                              hwce_interrupt_i,
                              ext_interrupt_i ,
                              dma_interrupt_i,
                              tmr_interrupt_i,
                              GP_interrupt_i,
                              barrier_interrupt_i};

   //**********************************************************
   //*************** MASK REGISTER ****************
   //**********************************************************
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if (rst_ni == 1'b0)
          begin
             r_interrupt_mask_low <= 'b0;
             r_interrupt_mask_high <= 'b0;
          end
        else
          begin
             if( s_interrupt_mask_sel_low == 1 )
               begin
                  r_interrupt_mask_low <= s_interrupt_mask_low;
               end
             if( s_interrupt_mask_sel_high == 1 )
               begin
                  r_interrupt_mask_high <= s_interrupt_mask_high;
               end
          end
     end

   //**********************************************************
   //*************** EMERGENCY IRQ EDGE DETECTOR ****************
   //**********************************************************
   assign emergency_clear = emergency_interrupt_clear_i;
   assign s_emergency_interrupt = emergency_interrupt_i;

   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if (rst_ni == 1'b0)
          begin
             r_emergency_interrupt <= 'b0;
          end
        else
          begin
             r_emergency_interrupt <= s_emergency_interrupt;
          end
     end

   assign emergency_interrupt_detected =~(r_emergency_interrupt) & s_emergency_interrupt;

   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if ( (rst_ni) == 1'b0)
          begin
             r_emergency_interrupt_buff <= 1'b0;
          end
        else
          begin
             case ({emergency_clear,emergency_interrupt_detected})
               2'b00:
                 begin
                    r_emergency_interrupt_buff <= r_emergency_interrupt_buff;
                 end

               2'b01:
                 begin
                    r_emergency_interrupt_buff <= s_emergency_interrupt;
                 end

               2'b10:
                 begin
                    r_emergency_interrupt_buff <= 1'b0;
                 end

               2'b11:
                 begin
                    r_emergency_interrupt_buff <= 1'b0;
                 end
             endcase
          end

     end


   //**********************************************************
   //*************** GP IRQ EDGE DETECTOR ****************
   //**********************************************************

   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if (rst_ni == 1'b0)
          begin
             r_interrupt_low <= 'b0;
          end
        else
          begin
             r_interrupt_low <= s_interrupt_low;
          end
     end

   assign edge_detected_low =~(r_interrupt_low) & s_interrupt_low;

   generate
      for( i=0; i<32; i++)
        begin : GP_interrupts_buff
           always_ff @(posedge clk_i, negedge rst_ni)
             begin
                if ( (rst_ni) == 1'b0)
                  begin
                     r_interrupt_buff_low[i] <= 1'b0;
                  end
                else
                  begin
                     case ({s_interrupt_buffer_clear_low[i],edge_detected_low[i]})
                       2'b00:
                         begin
                            r_interrupt_buff_low[i] <= r_interrupt_buff_low[i];
                         end

                       2'b01:
                         begin
                            r_interrupt_buff_low[i] <= s_interrupt_low[i];
                         end

                       2'b10:
                         begin
                            r_interrupt_buff_low[i] <= 1'b0;
                         end

                       2'b11:
                         begin
                            r_interrupt_buff_low[i] <= 1'b0;
                         end
                     endcase
                  end

             end
        end
   endgenerate

   assign r_interrupt_masked_low = r_interrupt_buff_low & r_interrupt_mask_low;

   always_comb
     begin
        if( r_interrupt_masked_low != 0 )
          r_interrupt_detected_low = 1;
        else
          r_interrupt_detected_low = 0;
     end

endmodule
