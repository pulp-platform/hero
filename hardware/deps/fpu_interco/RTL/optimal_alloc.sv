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
// Module Name:    optimal_alloc                                              //
// Project Name:   VEGA                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:                                                               //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 06/07/2011 : File Created                                  //
//                                                                            //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module optimal_alloc
#(
    parameter NB_CORES         = 4,
    parameter NB_APUS          = 2
)
(
    // CORE SIDE: Slave port
    input  logic [NB_CORES-1:0]                           req_i,
    output logic [NB_CORES-1:0][$clog2(NB_APUS)-1:0]      ROUTING_ADDR_o
);


	logic [$clog2(NB_CORES):0]                       num_request;
	

	generate


		// Count how many request we have in thiis cycle
		always_comb
		begin
			num_request  = 0;
			ROUTING_ADDR_o = '0;

			for(int unsigned j=0; j<NB_CORES; j++)
			begin
				if(req_i[j])
				begin
					ROUTING_ADDR_o[j] = num_request; // Blocking
					num_request       = num_request + 1;
				end
			end
		end




	endgenerate
endmodule