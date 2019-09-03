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

module axi2mem_tcdm_synch
(
   input  logic            clk_i,
   input  logic            rst_ni,
   input  logic            test_en_i,

   input  logic [1:0]      synch_req_i,
   input  logic [1:0][5:0] synch_id_i,

   input  logic            synch_gnt_i,
   output logic            synch_req_o,
   output logic [5:0]      synch_id_o
);

   logic [1:0]             s_synch_req;
   logic                   s_synch_gnt;
   logic [1:0][5:0]        s_synch_id;
   
   genvar  i;
   generate
      for (i=0; i<2; i++)
      begin : synch
         generic_fifo
         #(
            .DATA_WIDTH   ( 6                           ),
            .DATA_DEPTH   ( 2                           ) // IMPORTANT: DATA DEPTH MUST BE THE SAME AS CMD QUEUE DATA DEPTH
         )
         synch_i
         (
            .clk          ( clk_i                       ),
            .rst_n        ( rst_ni                      ),
            .test_mode_i  ( test_en_i                   ),

            .data_i       ( synch_id_i[i]               ),
            .valid_i      ( synch_req_i[i]              ),
            .grant_o      (                             ),

            .data_o       ( s_synch_id[i]               ),
            .valid_o      ( s_synch_req[i]              ),
            .grant_i      ( s_synch_gnt && synch_gnt_i  )
         );
      end
   endgenerate


   
   assign s_synch_gnt = s_synch_req[0] & s_synch_req[1];
   
   assign synch_req_o = s_synch_gnt;
   assign synch_id_o  = s_synch_id[0];
   
endmodule
