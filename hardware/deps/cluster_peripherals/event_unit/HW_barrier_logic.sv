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
// Module Name:    HW_barrier_logic                                           //
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

module HW_barrier_logic
  #(
    parameter NUM_CORES=4
    )
   ( 
     input logic                        clk_i,
     input logic                        rst_ni,
     input logic                        barrier_get_i,
     input logic[$clog2(NUM_CORES):0]   team_num_threads_i,
     input logic[NUM_CORES-1:0]         mask_to_trigger_i, 
     input logic                        store_team_data_i,
     input logic                        clear_req_i,
     output logic[NUM_CORES-1:0]        barrier_event_o,
     output logic[$clog2(NUM_CORES):0]  barrier_counter_o
     );

   genvar                               i;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                         TEAM_REGISTER                                    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

   logic [$clog2(NUM_CORES):0]         r_num_threads;
   logic [NUM_CORES-1:0]               r_mask_to_trigger;
   
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if ( rst_ni == 1'b0) 
          begin
             r_num_threads     <= 'b0;
             r_mask_to_trigger <= 'b0;
          end
        else 
          begin
             if( store_team_data_i == 1 )
               begin
                  r_num_threads     <= team_num_threads_i;
                  r_mask_to_trigger <= mask_to_trigger_i;
               end
          end
     end
 
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                              COUNTER                                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

   logic[$clog2(NUM_CORES):0] r_count;
   logic                      clear_counter;
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if ( rst_ni == 1'b0) 
          begin
             r_count <= 'b0;
          end
        else 
          begin
             if( barrier_get_i == 1 )
               begin
                  r_count <= r_count+1;
               end
             if( clear_counter | clear_req_i )
               begin
                  r_count <= 'b0;
               end
          end
     end 

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                        BARRIER_AND_MASK                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

   always_comb
     begin
        if( (r_count == r_num_threads)&(r_num_threads!=0) )
          begin
             barrier_event_o = r_mask_to_trigger;
             clear_counter   = 1;
          end
        else
          begin
             barrier_event_o = 'b0;
             clear_counter   = 0;
          end
     end

   assign barrier_counter_o = r_count;
   
endmodule
