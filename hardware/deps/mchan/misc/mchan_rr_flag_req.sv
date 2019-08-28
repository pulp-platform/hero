// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Igor Loi <igor.loi@unibo.it>
// Davide Rossi <davide.rossi@unibo.it>

module mchan_rr_flag_req
  #(
    parameter WIDTH = 3
    )
   (
    input  logic 			clk,
    input  logic 			rst_n,
    output logic [WIDTH-1:0] 	RR_FLAG_req_o,
    input  logic			req_i,
    input  logic			gnt_i
    );
   
   always_ff @(posedge clk, negedge rst_n)
     begin : RR_Flag_Req_SEQ
	if(rst_n == 1'b0)
	  RR_FLAG_req_o <= '0;
	else
	  if( req_i & gnt_i)
	    RR_FLAG_req_o <= RR_FLAG_req_o + 1'b1;
     end
   
endmodule
