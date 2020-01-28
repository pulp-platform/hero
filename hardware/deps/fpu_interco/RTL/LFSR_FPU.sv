////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Copyright 2018 ETH Zurich and University of Bologna.                       //
// Copyright and related rights are licensed under the Solderpad Hardware     //
// License, Version 0.51 (the "License"); you may not use this file except in //
// compliance with the License.  You may obtain a copy of the License at      //
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law  //
// or agreed to in writing, software, hardware and materials distributed under//
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR     //
// CONDITIONS OF ANY KIND, either express or implied. See the License for the //
// specific language governing permissions and limitations under the License. //
//                                                                            //
// Company:        Micrel Lab @ DEIS - University of Bologna                  //
//                    Viale Risorgimento 2 40136                              //
//                    Bologna - fax 0512093785 -                              //
//                                                                            //
// Engineer:       Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    01/01/2019                                                 //
// Design Name:    FPU_INTERCONNECT                                           //
// Module Name:    LFSR_FPU                                                   //
// Project Name:   VEGA                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:                                                               //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 01/01/2019 : File Created                                  //
//                                                                            //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


module LFSR_FPU 
#(
    parameter ADDR_WIDTH = 4,
    parameter SEED = 8'b00000000
) 
(
    output logic [ADDR_WIDTH-1:0] 	addr_o,
    input  logic 			enable_i,
    input  logic			clk,
    input  logic			rst_n
);


logic [7:0] 	out;
logic           linear_feedback;

assign addr_o = out[ADDR_WIDTH-1:0];

//-------------Code Starts Here-------
assign linear_feedback = !(out[7] ^ out[3]); // TAPS for XOR feedback

always @(posedge clk, negedge rst_n)
begin
    if (rst_n == 1'b0)
    begin // active high reset
      out <= SEED ;
    end 
    else if (enable_i) 
	 begin
	    out <= {out[6],out[5],out[4],out[3],out[2],out[1],out[0], linear_feedback};
	 end 

end



endmodule // End Of Module counter