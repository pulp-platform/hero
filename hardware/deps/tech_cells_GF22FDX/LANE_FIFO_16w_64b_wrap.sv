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

module LANE_FIFO_16w_64b_wrap
#(
   parameter ADDR_WIDTH = 4,
   parameter DATA_WIDTH = 64
)
(
   input  logic                        clk_a, // Clock
   input  logic                        cen_a_i,
   input  logic [ADDR_WIDTH-1:0]       addr_a_i,
   input  logic [DATA_WIDTH-1:0]       data_a_i,


   input  logic                        clk_b, // Clock
   input  logic                        cen_b_i,
   output logic [DATA_WIDTH-1:0]       data_b_o,
   input  logic [ADDR_WIDTH-1:0]       addr_b_i
);

   logic [2:0]  s_AW_A;
   logic        s_AC_A;

   logic [2:0]  s_AW_B;
   logic        s_AC_B;

   logic [DATA_WIDTH-1:0]  write_mask;

   assign write_mask = (cen_a_i) ?  '0 : '1;

   assign { s_AW_A, s_AC_A } = addr_a_i;
   assign { s_AW_B, s_AC_B } = addr_b_i;


   // R2PU
   LANE_FIFO_16w_64b i_LANE_FIFO_16w_64b
   (
      .CLK_A      ( clk_b       ), // READ_CLOCK
      .CEN_A      ( cen_b_i     ),
      .AW_A       ( s_AW_B      ),
      .AC_A       ( s_AC_B      ),
      .Q          ( data_b_o    ),

      .CLK_B      ( clk_a       ), // WRITE_CLOCK
      .CEN_B      ( cen_a_i     ),
      .AW_B       ( s_AW_A      ),
      .AC_B       ( s_AC_A      ),
      .D          ( data_a_i    ),
      .BW         ( write_mask  ),

      .DEEPSLEEP  ( 1'b0        ),
      .POWERGATE  ( 1'b0        ),

      .T_LOGIC    ( 1'b0        ),
      .MA_SAWL    ( '0          ),
      .MA_WL      ( '0          ),
      .MA_WRAS    ( '0          ),
      .MA_WRASD   ( '0          ),
      .MA_TPA     ( '0          ),
      .MA_TPB     ( '0          ),

      .OBSV_DBW   (             ),
      .OBSV_CTL_A (             ),
      .OBSV_CTL_B (             )
   );

endmodule