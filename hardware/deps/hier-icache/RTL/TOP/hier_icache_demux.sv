// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module hier_icache_demux
#(
    parameter FETCH_ADDR_WIDTH = 32,
    parameter FETCH_DATA_WIDTH = 128
)
(
    input logic                                clk,
    input logic                                rst_n,
    input logic                                destination_i,

    // signals from PRI cache and interconnect
    input  logic                               refill_req_i,
    output logic                               refill_gnt_o,
    input  logic  [FETCH_ADDR_WIDTH-1:0]       refill_addr_i,
    output logic                               refill_r_valid_o,
    output logic  [FETCH_DATA_WIDTH-1:0]       refill_r_data_o,

   
    // signals from PRI cache and interconnect
    output logic [1:0]                          refill_req_o,
    input  logic [1:0]                          refill_gnt_i,
    output logic [1:0] [FETCH_ADDR_WIDTH-1:0]   refill_addr_o,
    input  logic [1:0]                          refill_r_valid_i,
    input  logic [1:0] [FETCH_DATA_WIDTH-1:0]   refill_r_data_i
);



    assign refill_req_o[0]   = (destination_i == 1'b0 ) ? refill_req_i  : 1'b0;
    assign refill_addr_o[0]  = (destination_i == 1'b0 ) ? refill_addr_i : '0;

    assign refill_req_o[1]   = (destination_i == 1'b1 ) ? refill_req_i  : 1'b0;
    assign refill_addr_o[1]  = (destination_i == 1'b1 ) ? refill_addr_i : '0;

    assign refill_gnt_o      = refill_gnt_i[destination_i];
    assign refill_r_valid_o  = refill_r_valid_i[destination_i];
    assign refill_r_data_o   = refill_r_data_i[destination_i];

endmodule
