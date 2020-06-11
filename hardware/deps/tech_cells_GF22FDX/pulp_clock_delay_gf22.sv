// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

//andy hack: support different standard cell libraries by setting `GF_TRACK,
//`GF_VT and `GF_LEN
// SC8T_CKGPRELATNX1_CSC24L
// SC8T_BUFX3_CSC20L



module pulp_clock_delay
(
   input  logic in_i,
   output logic out_o
);

    logic taps_0;
    logic taps_1;


    SC8T_DLY100X1_CSC20L u_delay_rds_0
    (
        .A ( in_i         ),
        .Z ( taps_0       )
    );

    SC8T_BUFX1_CSC24L clk_inv_i_0
    (
       .A(taps_0),
       .Z(taps_1)
    );

    SC8T_BUFX3_CSC24L clk_inv_i_1
    (
       .A(taps_1),
       .Z(out_o)
    );


endmodule // pulp_clock_delay
