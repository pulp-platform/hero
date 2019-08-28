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
// Module Name:    HWBarrier                                                  //
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

module HW_barrier
#(
    parameter NUM_CORES=4
)
( 
    input  logic                                                clk_i,
    input  logic                                                rst_ni,
    input  logic [`NUM_BARRIERS-1:0]                            barrier_get_i,
    input  logic [`NUM_BARRIERS-1:0][$clog2(NUM_CORES):0]       team_num_threads_i,
    input  logic [`NUM_BARRIERS-1:0][NUM_CORES-1:0]             mask_to_trigger_i,
    input  logic [`NUM_BARRIERS-1:0]                            store_team_data_i, 
    input  logic [`NUM_BARRIERS-1:0]                            clear_barrier_req_i, 
    output logic [NUM_CORES-1:0]                                barrier_event_o,
    output logic [`NUM_BARRIERS-1:0][$clog2(NUM_CORES):0]       barrier_counter_o
); 

   genvar                                                 i;
   logic [`NUM_BARRIERS-1:0][NUM_CORES-1:0]               s_barrier_event;
   logic [NUM_CORES-1:0][`NUM_BARRIERS-1:0]               s_barrier_transposed_event;
   logic [NUM_CORES-1:0]                                  internal_event;
   logic [`NUM_BARRIERS-1:0][$clog2(NUM_CORES):0]         barrier_counter;
   //////////////////////////////////////////////////////////////////////////////
   //   //
   //   //
   //       STATUS_REGISTER  //
   //   //
   //   //
   //////////////////////////////////////////////////////////////////////////////
   /*

    assign toggle_status = barrier_get_i | barrier_event_o;


    generate
    for(i=0; i<NUM_CORES; i++)
    begin 
   always_ff @(posedge clk_i, negedge rst_ni)
    begin
   if ( (rst_ni) == 1'b0) 
   begin
   r_status[i] <= 1'b0;
  end
   else 
   begin
   if ( toggle_status[i] == 1) 
   begin
   r_status[i] <= !r_status[i];
      end
    end

 end 
 end 
 endgenerate 
    */
   //////////////////////////////////////////////////////////////////////////////
   //   //
   //   //
   //       HW_BARRIER_GENERATE  //
   //   //
   //   //
   //////////////////////////////////////////////////////////////////////////////

   generate
     for ( i = 0; i < `NUM_BARRIERS; i++ ) begin : HW_bar
         HW_barrier_logic
         #(
             .NUM_CORES(NUM_CORES)
         )
         HW_barrier_logic_i
         ( 
             .clk_i(clk_i),
             .rst_ni(rst_ni),
             .barrier_get_i( barrier_get_i[i] ),
             .team_num_threads_i(team_num_threads_i[i]),
             .mask_to_trigger_i( mask_to_trigger_i[i] ), 
             .store_team_data_i( store_team_data_i[i] ),
             .clear_req_i(clear_barrier_req_i[i]),
             .barrier_event_o(s_barrier_event[i]),
             .barrier_counter_o( barrier_counter[i] )
         );
     end
   endgenerate



   always_comb
     begin
        for( int i = 0; i<NUM_CORES; i++)
          begin
             for( int j = 0; j<`NUM_BARRIERS; j++)
               begin
                  s_barrier_transposed_event[i][j] = s_barrier_event[j][i];
               end
          end
     end

   always_comb
     begin
        for( int i = 0; i<NUM_CORES; i++)
          begin
            if( s_barrier_transposed_event[i] != 0 ) 
              internal_event[i] = 1'b1;
            else
              internal_event[i] = 1'b0;
          end
     end
   logic [NUM_CORES-1:0] r_barrier_event;

   /*always_ff @(posedge clk_i, negedge rst_ni)
    begin
    if ( (rst_ni) == 1'b0) 
    r_barrier_event <= 'b0;
    else 
    r_barrier_event <= internal_event;// | barrier_event_from_event_unit_i; //has to be added with master/slave barriers
end*/
   assign barrier_event_o   = internal_event;
   assign barrier_counter_o = barrier_counter;
   
endmodule

