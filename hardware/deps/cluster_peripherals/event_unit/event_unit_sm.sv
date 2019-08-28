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
// Module Name:    event_unit_sm                                              //
// Project Name:   PULP                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:                                                               //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
`include "old_event_unit_defines.sv"

module event_unit_sm
#(
    parameter NUM_CORES=4
)
(
   input logic                   clk_i,
   input logic                   rst_ni,
   input logic                   s_clk_stop_i,
   input logic                   ready_to_shutdown_i,
   input logic                   r_event_detect_i,
   input logic                   IRQ_i,
   output logic                  fetch_en_o,

`ifdef FEATURE_IDLE_CNT
   input logic                   clear_cnt_i,
   input logic                   start_cnt_i,
   output logic[31:0]            idle_cyc_cnt_o,
`endif
   output logic                  clk_gate_core_o
);

   logic               clk_gate_core;
   logic               fetch_en_core;
   enum   logic[1:0]   { RUN,WAIT_4_SHUTDOWN,CLK_OFF} CS_CLK,NS_CLK;

   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if (~rst_ni)
          begin
             CS_CLK <= RUN;
          end
        else
          begin
             CS_CLK <= NS_CLK;
          end
     end

   always_comb
   begin
        clk_gate_core = 1'b0;
        fetch_en_core = 1'b0;
        NS_CLK        = CS_CLK;

        case(CS_CLK)
          RUN:
          begin
             fetch_en_core = 1'b1;

             if ( s_clk_stop_i && !r_event_detect_i)
               NS_CLK = WAIT_4_SHUTDOWN;
          end

          WAIT_4_SHUTDOWN:
          begin
             if ( r_event_detect_i )
               NS_CLK = RUN;
             else if ( (!ready_to_shutdown_i) && (!IRQ_i))
               NS_CLK = CLK_OFF;
          end

          CLK_OFF:
          begin
             clk_gate_core = 1'b1;

             if ( r_event_detect_i )
               NS_CLK = RUN;
             else if ( IRQ_i )
               NS_CLK = WAIT_4_SHUTDOWN;
          end

          default:
          begin
             NS_CLK = RUN;
          end
        endcase
   end

`ifdef FEATURE_IDLE_CNT
   logic[31:0] r_idle_cyc_cnt;
   logic       r_start_cnt,edge_detected;
   logic       cnt_running;

   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if ( rst_ni == 1'b0)
          begin
             r_start_cnt <= 'b0;
          end
        else
          begin
             r_start_cnt <= start_cnt_i;
          end
     end
   assign edge_detected = (!r_start_cnt) & start_cnt_i;

   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if ( rst_ni == 1'b0)
          begin
             cnt_running <= 'b0;
          end
        else
          begin
             if(edge_detected)
               begin
                  cnt_running <= ~cnt_running;
               end
          end
     end

   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if ( rst_ni == 1'b0)
          begin
             r_idle_cyc_cnt <= 'b0;
          end
        else
          begin
             if( (CS_CLK == CLK_OFF)&(cnt_running) )
               begin
                  r_idle_cyc_cnt <= r_idle_cyc_cnt+1;
               end
             if( clear_cnt_i == 1 )
               begin
                  r_idle_cyc_cnt <= 'b0;
               end
          end
     end
   assign idle_cyc_cnt_o  =  r_idle_cyc_cnt;
`endif
   assign fetch_en_o      = fetch_en_core;
   assign clk_gate_core_o = clk_gate_core;

endmodule

