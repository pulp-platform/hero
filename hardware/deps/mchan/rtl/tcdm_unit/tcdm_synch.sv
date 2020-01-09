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

module tcdm_synch
#(
      parameter TRANS_SID_WIDTH = 2
)
(

      input  logic                            clk_i,
      input  logic                            rst_ni,

      input  logic                            test_mode_i,

      input  logic [1:0]                      synch_req_i,
      input  logic [1:0][TRANS_SID_WIDTH-1:0] synch_sid_i,

      output logic                            synch_req_o,
      output logic [TRANS_SID_WIDTH-1:0]      synch_sid_o

);
   
   logic [1:0]                               s_synch_req;
   logic                                     s_synch_gnt;
   logic [1:0][TRANS_SID_WIDTH-1:0]          s_synch_sid;
   
   genvar         i;
   
   generate
      for (i=0; i<2; i++)
      begin : synch
            generic_fifo
            #(
               .DATA_WIDTH(TRANS_SID_WIDTH),
               .DATA_DEPTH(2) // IMPORTANT: DATA DEPTH MUST BE THE SAME AS CMD QUEUE DATA DEPTH
            )
            synch_i
            (

               .clk         ( clk_i           ),
               .rst_n       ( rst_ni          ),

               .data_i      ( synch_sid_i[i]  ),
               .valid_i     ( synch_req_i[i]  ),
               .grant_o     (                 ),

               .data_o      ( s_synch_sid[i]  ),
               .grant_i     ( s_synch_gnt     ),
               .valid_o     ( s_synch_req[i]  ),

               .test_mode_i ( test_mode_i     )

            );
      end
   endgenerate
   
   assign s_synch_gnt = s_synch_req[0] & s_synch_req[1];
   
   assign synch_req_o = s_synch_gnt;
   assign synch_sid_o = s_synch_sid[0];
   
endmodule
