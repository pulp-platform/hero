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
// Module Name:    AddressDecoder_Req_FPU                                     //
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


module AddressDecoder_Req_FPU
#(
    parameter ID_WIDTH            = 8,
    parameter NB_APUS             = 16,
    parameter USE_OPT_ALLOC       = "TRUE",
    parameter int unsigned  ID    = 1,
    parameter int unsigned  SEED  = 7
) 
(
    input  logic                                 clk,
    input  logic                                 rst_n,
    input  logic                                 data_req_i,    // Request from Master
    input  logic [$clog2(NB_APUS)-1:0]           ROUTING_ADDR_i,  
    input  logic [NB_APUS-1:0]                   apu_status_i,  // Address from Master
    output logic                                 data_gnt_o,    // Grant delivered to Master

    // ARB TREE SIDE
    input  logic [NB_APUS-1:0]                   data_gnt_i,    // Grant Array: one for each memory on ARB TREE SIDE
    output logic [NB_APUS-1:0]                   data_req_o,    // Request Array: one for each memory
    output logic [ID_WIDTH-1:0]                  data_ID_o      // data_ID_o is sent whit the request (like a PID)
);

      localparam LOG_SLAVE  = $clog2(NB_APUS);

      logic [LOG_SLAVE-1:0]   RANDOM_ADDR, ROUTING_ADDR;

      assign data_ID_o = ID;            // ID is simply attached to the ID_OUT

 
generate
    if(NB_APUS>1)
    begin : MULTI_APU
      
      LFSR_FPU #( .ADDR_WIDTH(LOG_SLAVE), .SEED(SEED+ID) ) RANDOM_ADDR_GEN
      (
          .addr_o   ( RANDOM_ADDR            ),
          .enable_i ( data_req_i & data_gnt_o ),
          .clk      ( clk                     ),
          .rst_n    ( rst_n                   )
      );

      if(USE_OPT_ALLOC == "TRUE" )
      begin
        assign ROUTING_ADDR = ROUTING_ADDR_i;
      end
      else
      begin
        // Make sure that the routing addres is < NB_APU/
        assign ROUTING_ADDR = (RANDOM_ADDR >= NB_APUS) ? ~RANDOM_ADDR : RANDOM_ADDR;
      end

      always @(*)
      begin : Combinational_ADDR_DEC_REQ
         //DEFAULT VALUES
         data_req_o  = '0;
         data_gnt_o  = 1'b0;


         data_req_o[ROUTING_ADDR] = data_req_i;
         data_gnt_o = data_gnt_i[ROUTING_ADDR];
      end

    end
    else
    begin : MONO_APU
      always @(*)
      begin
             data_req_o[0] = data_req_i;
             data_gnt_o    = data_gnt_i[0];
      end
    end
endgenerate




endmodule
