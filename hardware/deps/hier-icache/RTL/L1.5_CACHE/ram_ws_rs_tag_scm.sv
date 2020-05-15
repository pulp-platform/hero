// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


// `define  USE_SRAM


module ram_ws_rs_tag_scm
#(
    parameter data_width = 7,
    parameter addr_width = 6
)
(
    input  logic                     clk,
    input  logic                     rst_n,
    input  logic                     test_en_i,
    input  logic  [addr_width-1:0]   addr,
    input  logic                     req,
    input  logic                     write,
    input  logic [data_width-1:0]    wdata,
    output logic [data_width-1:0]    rdata
);

`ifdef USE_TAG_SRAM
    logic cs_n;
    logic we_n;

    assign  cs_n = ~req;
    assign  we_n = ~write;

    generate
      if(data_width==10 && addr_width==5)
      begin : SRAM_CUT

        logic [2:0]     n_aw;
        logic [1:0]     n_ac;
        logic [9:0]     bw;
        assign {n_aw, n_ac} = addr;
        assign bw = (we_n) ? '0 : '1;

        // GF22
        SPREG_32w_10b sram_tag
        (

            .CLK      ( clk   ), // input
            .CEN      ( cs_n  ), // input
            .RDWEN    ( we_n  ), // input
            .AW       ( n_aw  ), // input [3:0]
            .AC       ( n_ac  ), // input
            .D        ( wdata ), // input [9:0]
            .BW       ( '1    ), // input [9:0]
            .T_LOGIC  ( 1'b0  ), // input
            .MA_SAWL  ( '0    ), // input
            .MA_WL    ( '0    ), // input
            .MA_WRAS  ( '0    ), // input
            .MA_WRASD ( '0    ), // input
            .Q        ( rdata ), // output [9:0]
            .OBSV_CTL (       )  // output
        );
/*
          SRAM_SP_32w_10b sram_tag
          (
            .CS_N    ( cs_n  ),
            .CLK     ( clk   ),
            .WR_N    ( we_n  ),
            .RW_ADDR ( addr  ),
            .RST_N   ( rst_n ),
            .DATA_IN ( wdata ),
            .DATA_OUT( rdata )
          );
*/
      end


    endgenerate

`else
   `ifdef PULP_FPGA_EMUL
      register_file_1r_1w
   `else
      register_file_1r_1w_test_wrap
   `endif
      #(
        .ADDR_WIDTH(addr_width),
        .DATA_WIDTH(data_width)
      )
      scm_tag
      (
        .clk           (clk),
  `ifdef PULP_FPGA_EMUL
        .rst_n         (rst_n),
  `endif
        .test_en_i,

        // Read port
        .ReadEnable  ( req & ~write ),
        .ReadAddr    ( addr         ),
        .ReadData    ( rdata        ),

        // Write port
        .WriteEnable ( req & write  ),
        .WriteAddr   ( addr         ),
        .WriteData   ( wdata        )
      );
`endif

endmodule
