// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
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
// Create Date:    22/01/2018                                                 //
// Design Name:    icache_intc                                                //
// Module Name:    Resp_Arb_Node_icache_intc.sv                               //
// Project Name:   MrWolf                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:   fan_out primitive (routing only) used to route responses    //
//                                                                            //
// Revision v0.1 - 16/02/2018 : File Created                                  //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module Resp_Arb_Node_icache_intc #( parameter DATA_WIDTH = 32 )
(
    input  logic                  response_ch0_i,
    input  logic [DATA_WIDTH-1:0] read_data_ch0_i,

    input  logic                  response_ch1_i,
    input  logic [DATA_WIDTH-1:0] read_data_ch1_i,

    output logic [DATA_WIDTH-1:0] read_data_o,
    output logic                  response_o
);
    assign response_o  = response_ch0_i | response_ch1_i;
    assign read_data_o = (response_ch1_i) ? read_data_ch1_i : read_data_ch0_i;
endmodule
