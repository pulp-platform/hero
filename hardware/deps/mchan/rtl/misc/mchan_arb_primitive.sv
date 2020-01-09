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

module mchan_arb_primitive 
#(
    parameter DATA_WIDTH = 32,
    parameter ID_WIDTH   = 4
)
(
    input  logic                   RR_FLAG,

    

    // LEFT SIDE
    input  logic                   req0_i,
    input  logic                   req1_i,      
    output logic                   gnt0_o,
    output logic                   gnt1_o,
    input  logic [DATA_WIDTH-1:0]  data0_i,
    input  logic [DATA_WIDTH-1:0]  data1_i,
    input  logic [ID_WIDTH-1:0]    id0_i,
    input  logic [ID_WIDTH-1:0]    id1_i,



    // RIGTH SIDE
    output logic                   req_o,
    input  logic                   gnt_i,
    output logic [DATA_WIDTH-1:0]  data_o,
    output logic [ID_WIDTH-1:0]    id_o

);
   logic                   sel;

   assign req_o  = req0_i | req1_i;
   assign sel    = ~req0_i | ( RR_FLAG & req1_i); // SEL FOR ROUND ROBIN MUX
   assign gnt0_o = (( req0_i & ~req1_i) | ( req0_i & ~RR_FLAG)) & gnt_i;
   assign gnt1_o = ((~req0_i &  req1_i) | ( req1_i &  RR_FLAG)) & gnt_i;
   
   assign data_o = sel   ? data1_i : data0_i;
   assign id_o   = sel   ? id1_i   : id0_i;
   
endmodule
