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
//                 Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Create Date:    12/03/2015                                                 //
// Design Name:    event_unit                                                 //
// Module Name:    event_unit_arbiter                                         //
// Project Name:   PULP                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    arbiter for event unit                                     //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (18/03/2015) removed Comb loop in   IRQ_id_o, added a reg  //
//                  to hold previous value.                                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
`include "old_event_unit_defines.sv"

module interrupt_id_arbiter
#(
    parameter NUM_CORES=4
)
(
     input  logic[63:0] interrupt_buffer_status_i,
     output logic[7:0]  IRQ_id_o
);

   always_comb
   begin
        IRQ_id_o = 8'hFF; //means no pending IRQs

        begin
             for (int i = 63; i >= 0 ; i--)
             begin
                  if( interrupt_buffer_status_i[i] == 1'b1)
                  begin
                       IRQ_id_o = i;
                  end
             end
        end
   end

endmodule
