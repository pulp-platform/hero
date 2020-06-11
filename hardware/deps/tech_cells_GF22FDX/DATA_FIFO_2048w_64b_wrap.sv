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

module DATA_FIFO_2048w_64b_wrap
#(
   parameter ADDR_WIDTH = 11,
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


   logic [6:0]  s_AW_A;
   logic [1:0]  s_AC_A;
   logic [6:0]  s_AW_B;
   logic [1:0]  s_AC_B;

   logic [DATA_WIDTH-1:0]       write_mask;
   logic [3:0]                  s_cen_a, s_cen_b;
   logic [1:0]                  r_dest; 
   logic [3:0][DATA_WIDTH-1:0]  s_data_b;

   assign write_mask = (cen_a_i) ?  '0 : '1;

   assign { s_AW_A, s_AC_A } = addr_a_i[8:0];
   assign { s_AW_B, s_AC_B } = addr_b_i[8:0];



   assign s_cen_a[0] = (addr_a_i[10:9] == 2'b00) ? cen_a_i : 1'b1;
   assign s_cen_a[1] = (addr_a_i[10:9] == 2'b01) ? cen_a_i : 1'b1;
   assign s_cen_a[2] = (addr_a_i[10:9] == 2'b10) ? cen_a_i : 1'b1;
   assign s_cen_a[3] = (addr_a_i[10:9] == 2'b11) ? cen_a_i : 1'b1;

   assign s_cen_b[0] = (addr_b_i[10:9] == 2'b00) ? cen_b_i : 1'b1;
   assign s_cen_b[1] = (addr_b_i[10:9] == 2'b01) ? cen_b_i : 1'b1;
   assign s_cen_b[2] = (addr_b_i[10:9] == 2'b10) ? cen_b_i : 1'b1;
   assign s_cen_b[3] = (addr_b_i[10:9] == 2'b11) ? cen_b_i : 1'b1;




   always_ff @(posedge clk_b ) 
   begin
      r_dest <= addr_b_i[10:9];
   end

   assign data_b_o = s_data_b[r_dest];

   genvar i;
   generate 
      for(i=0; i<4; i++)
      begin : DP_CUT

            DATA_FIFO_512w_64b i_DATA_FIFO_512w_64b
            (
               .CLK_A      ( clk_b        ), // READ_CLOCK
               .CEN_A      ( s_cen_b[i]   ), 
               .AW_A       ( s_AW_B       ),
               .AC_A       ( s_AC_B       ),
               .Q          ( s_data_b[i]  ),
               
               .CLK_B      ( clk_a        ), // WRITE CLOCK
               .CEN_B      ( s_cen_a[i]   ),
               .AW_B       ( s_AW_A       ),
               .AC_B       ( s_AC_A       ),
               .BW         ( write_mask   ),
               .D          ( data_a_i     ),

               .DEEPSLEEP  ( 1'b0         ),
               .POWERGATE  ( 1'b0         ),
               

               .T_LOGIC    ( '0           ),
               .MA_SAWL    ( '0           ),
               .MA_WL      ( '0           ),
               .MA_WRAS    ( '0           ),
               .MA_WRASD   ( '0           ),
               .MA_TPA     ( '0           ),
               .MA_TPB     ( '0           ),
               
               .OBSV_DBW   (              ),
               .OBSV_CTL_A (              ),
               .OBSV_CTL_B (              )

            );

      end
   endgenerate





endmodule