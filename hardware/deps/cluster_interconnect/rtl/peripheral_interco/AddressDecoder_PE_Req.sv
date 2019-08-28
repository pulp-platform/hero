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
// Create Date:    29/06/2011                                                 // 
// Design Name:    LOG_INTERCONNECT                                           // 
// Module Name:    AddressDecoder_PE_Req                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Address Decoder used to generate the individual requests   //
//                 for all the available memory cuts. It backroutes the       //
//                 grants from the Arbitration tree to the processor          //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - Code Restyling (19/02/2015)                                //
//                                                                            //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "parameters.v"

module AddressDecoder_PE_Req 
#(
    parameter int ID_WIDTH             = 17,    // ID WIDTH (number of bits) --> see ID comment
    parameter int ID                   = 1,     // ID routed with REQUEST used to backroute response
    parameter int N_SLAVE              = 16,    // Number of Memory cuts
    parameter int LOG_CLUSTER          = 5,
    parameter int ADDR_WIDTH           = 32,
    parameter int PE_ROUTING_LSB       = 16,
    parameter int PE_ROUTING_MSB       = 19,
    parameter bit CLUSTER_ALIAS        = 1'b0,
    parameter int CLUSTER_ALIAS_BASE   = 12'h000
) 
(
    input  logic [LOG_CLUSTER-1:0]               CLUSTER_ID,
    // MASTER SIDE
    input  logic                                 data_req_i,    // Request from Master
    input  logic [ADDR_WIDTH-1:0]                data_add_i,    // Address from Master
`ifdef GNT_BASED_FC
    output logic                                 data_gnt_o,    // Grant delivered to Master
    input  logic [N_SLAVE-1:0]                   data_gnt_i,    // Grant Array: one for each memory on ARB TREE SIDE
`else
    output logic                                 data_stall_o,  // Stall delivered to Master
    input  logic [N_SLAVE-1:0]                   data_stall_i,  // Stall Array: one for each memory on ARB TREE SIDE
`endif
    // ARB TREE SIDE
    output logic [N_SLAVE-1:0]                   data_req_o,    // Request Array: one for each memory
    output logic [ID_WIDTH-1:0]                  data_ID_o      // data_ID_o is sent whit the request (like a PID)
);

      localparam LOG_SLAVE  = `log2(N_SLAVE-1);

      logic      [LOG_SLAVE-1:0]                  ROUTING_ADDR;      // M = Number of memory cuts

      logic [11:0]                            PE_END;
      logic [11:0]                            PE_START;

      assign data_ID_o = ID;            // ID is simply attached to the ID_OUT

      assign PE_START   = 12'h100 + (CLUSTER_ID << 2) + 2;
      assign PE_END     = 12'h100 + (CLUSTER_ID << 2) + 3;

      always_comb begin
         if (data_add_i[31:20] >= PE_START && data_add_i[31:20] < PE_END
            || (CLUSTER_ALIAS
               && data_add_i[31:20] >= CLUSTER_ALIAS_BASE+2
               && data_add_i[31:20] < (CLUSTER_ALIAS_BASE+3)
            )
         ) begin
            ROUTING_ADDR = data_add_i[PE_ROUTING_MSB:PE_ROUTING_LSB];
         end else begin
            ROUTING_ADDR = '1;
         end
      end
   
      always_comb
      begin : Combinational_ADDR_DEC_REQ
         //DEFAULT VALUES
         data_req_o = '0;
         // Apply the rigth value
         data_req_o[ROUTING_ADDR] = data_req_i;
      `ifdef GNT_BASED_FC
         data_gnt_o = data_gnt_i[ROUTING_ADDR];
      `else
         data_stall_o = data_stall_i[ROUTING_ADDR];
      `endif
      end

endmodule
