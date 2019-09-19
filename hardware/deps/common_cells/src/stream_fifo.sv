// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module stream_fifo #(
    parameter bit          FALL_THROUGH = 1'b0, // fifo is in fall-through mode
    parameter int unsigned DEPTH        = 1,    // depth can be arbitrary from 0 to 2**32
    parameter type         T            = logic,
    // DO NOT OVERWRITE THIS PARAMETER
    parameter int unsigned ADDR_DEPTH   = (DEPTH > 1) ? $clog2(DEPTH) : 1
) (
    input  logic                    clk_i,          // clock
    input  logic                    rst_ni,         // asynchronous active-low reset
    input  logic                    flush_i,        // flush the FIFO
    input  logic                    testmode_i,     // test mode to bypass clock gating
    input  T                        data_i,         // data to push into the FIFO
    input  logic                    valid_i,        // input data is valid
    output logic                    ready_o,        // FIFO is ready to take input data
    output T                        data_o,         // data to pop from the FIFO
    output logic                    valid_o,        // output data is valid
    input  logic                    ready_i,        // downstream is ready to take output data
    output logic [ADDR_DEPTH-1:0]   usage_o         // fill pointer
);

    logic full, empty;
    fifo_v3 #(
        .FALL_THROUGH   ( FALL_THROUGH  ),
        .DATA_WIDTH     ( $bits(T)      ),
        .DEPTH          ( DEPTH         )
    ) i_fifo (
        .clk_i,
        .rst_ni,
        .flush_i,
        .testmode_i,
        .full_o     (full),
        .empty_o    (empty),
        .usage_o,
        .data_i,
        .push_i     (valid_i & ~full),
        .data_o,
        .pop_i      (ready_i & ~empty)
    );
    assign ready_o = ~full;
    assign valid_o = ~empty;

endmodule
