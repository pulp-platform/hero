// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Antonio Pullini <pullinia@iis.ee.ethz.ch>

module pulp_sync
#(
    parameter STAGES = 2
)
(
    input  logic clk_i,
    input  logic rstn_i,
    input  logic serial_i,
    output logic serial_o
);


generate
    case(STAGES)
    2: begin : SYNC_2_STAGES
        SC8T_SYNC2SDFFRQX4_CSC20L r_bf_synch2
        (
            .Q     ( serial_o ),
            .CLK   ( clk_i    ),
            .D     ( serial_i ),
            .RESET ( rstn_i   ),
            .SE    ( 1'b0     ),
            .SI    ( 1'b0     )
        );
    end

    3: begin : SYNC_3_STAGES
        SC8T_SYNC3SDFFRQX4_CSC20L r_bf_synch3
        (
            .Q     ( serial_o ),
            .CLK   ( clk_i    ),
            .D     ( serial_i ),
            .RESET ( rstn_i   ),
            .SE    ( 1'b0     ),
            .SI    ( 1'b0     )
        );
    end
    

    4: begin : SYNC_4_STAGES
        SC8T_SYNC4SDFFRQX4_CSC20L r_bf_synch4
        (
            .Q     ( serial_o ),
            .CLK   ( clk_i    ),
            .D     ( serial_i ),
            .RESET ( rstn_i   ),
            .SE    ( 1'b0     ),
            .SI    ( 1'b0     )
        );
    end

    endcase // STAGES
endgenerate

   
endmodule
