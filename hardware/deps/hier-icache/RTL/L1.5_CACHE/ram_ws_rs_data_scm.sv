// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


`include "pulp_soc_defines.sv"
// `define  USE_SRAM

module ram_ws_rs_data_scm
#(
    parameter data_width     = 64,
    parameter addr_width     = 7,
    parameter be_width       = data_width/8
)
(
    input  logic                        clk,
    input  logic                        rst_n,
    input  logic [addr_width-1:0]       addr,
    input  logic                        req,
    input  logic                        write,
    input  logic [be_width-1:0][7:0]    wdata,
    input  logic [be_width-1:0]         be,
    output logic [data_width-1:0]       rdata
);

`ifdef USE_DATA_SRAM

    logic cs_n;
    logic we_n;

    assign  cs_n = ~req;
    assign  we_n = ~write;

    generate
      if(data_width==128)
      begin : SRAM_CUT

        case (addr_width)
            5: begin
                logic [4-1:0]   n_aw;
                logic [1-1:0]   n_ac;
                logic [127:0]   bw;
                assign {n_aw, n_ac} = addr;
                assign bw = (we_n) ?  '0 : '1;

                // GF22
                SPREG_32w_128b sram_data
                (

                    .CLK      ( clk   ), // input
                    .CEN      ( cs_n  ), // input
                    .RDWEN    ( we_n  ), // input
                    .AW       ( n_aw  ), // input [3:0]
                    .AC       ( n_ac  ), // input
                    .D        ( wdata ), // input [127:0]
                    .BW       ( '1    ), // input [127:0]
                    .T_LOGIC  ( 1'b0  ), // input
                    .MA_SAWL  ( '0    ), // input
                    .MA_WL    ( '0    ), // input
                    .MA_WRAS  ( '0    ), // input
                    .MA_WRASD ( '0    ), // input
                    .Q        ( rdata ), // output [127:0]
                    .OBSV_CTL (       )  // output
                );

                // TSMC55
                // SRAM_SP_32w_128b sram_data
                // (
                //     .CS_N    ( cs_n  ),
                //     .CLK     ( clk   ),
                //     .WR_N    ( we_n  ),
                //     .RW_ADDR ( addr  ),
                //     .RST_N   ( rst_n ),
                //     .DATA_IN ( wdata ),
                //     .DATA_OUT( rdata )
                // );
            end

            6: begin
                logic          n_as;
                logic [2:0]    n_aw;
                logic [1:0]    n_ac;
                logic [127:0]   bw;
                assign {n_aw[2], n_as, n_aw[1:0], n_ac} = addr;
                assign bw = (we_n) ?  '0 : '1;

                SP1D_64w_128b sram_data
                (
                    .CLK         ( clk           ),
                    .CEN         ( cs_n          ),
                    .RDWEN       ( we_n          ),
                    .DEEPSLEEP   ( 1'b0          ),
                    .POWERGATE   ( 1'b0          ),
                    .AS          ( n_as          ),
                    .AW          ( n_aw          ),
                    .AC          ( n_ac          ),
                    .D           ( wdata         ),
                    .BW          ( bw            ),
                    .T_BIST      ( 1'b0          ),
                    .T_LOGIC     ( 1'b0          ),
                    .T_CEN       ( 1'b0          ),
                    .T_RDWEN     ( 1'b0          ),
                    .T_DEEPSLEEP ( 1'b0          ),
                    .T_POWERGATE ( 1'b0          ),
                    .T_STAB      ( '0            ),
                    .T_WBT       ( '0            ),
                    .T_AS        ( '0            ),
                    .T_AW        ( '0            ),
                    .T_AC        ( '0            ),
                    .T_D         ( '0            ),
                    .T_BW        ( '0            ),
                    .MA_SAWL     ( '0            ),
                    .MA_WL       ( '0            ),
                    .MA_WRAS     ( '0            ),
                    .MA_WRASD    ( '0            ),
                    .Q           ( rdata         ),
                    .OBSV_CTL    (               )
                );
            end
            default : /* default */;
        endcase

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
    scm_data
    (
        .clk         ( clk          ),
    `ifdef PULP_FPGA_EMUL
        .rst_n       ( rst_n        ),
    `endif

        // Read port
        .ReadEnable  ( req & ~write ),
        .ReadAddr    ( addr         ),
        .ReadData    ( rdata        ),

        // Write port
        .WriteEnable ( req & write  ),
        .WriteAddr   ( addr         ),
        .WriteData   ( wdata        )
    `ifndef PULP_FPGA_EMUL
        ,
        // BIST ENABLE
        .BIST        ( 1'b0                ), // PLEASE CONNECT ME;

        // BIST ports
        .CSN_T       (                     ), // PLEASE CONNECT ME; Synthesis will remove me if unconnected
        .WEN_T       (                     ), // PLEASE CONNECT ME; Synthesis will remove me if unconnected
        .A_T         (                     ), // PLEASE CONNECT ME; Synthesis will remove me if unconnected
        .D_T         (                     ), // PLEASE CONNECT ME; Synthesis will remove me if unconnected
        .Q_T         (                     )
    `endif
    );
`endif

endmodule
