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
`ifdef TARGET_SYNTHESIS
`define USE_DATA_SRAM
`endif

module ram_ws_rs_data_scm
#(
    parameter data_width     = 64,
    parameter addr_width     = 7,
    parameter be_width       = data_width/8
)
(
    input  logic                        clk,
    input  logic                        rst_n,
    input  logic                        test_en_i,
    input  logic [25:0]                 mem_ctrl,
    input  logic                        dft_ram_gt_se,
    input  logic                        dft_ram_bypass,
    input  logic                        dft_ram_bp_clk_en,
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

                IN22FDX_R1PH_NFHN_W00032B128M02C256 sram_data //
                (

                    .CLK          ( clk              ),
                    .CEN          ( cs_n             ),
                    .RDWEN        ( write            ),
                    .AW           ( addr[4:1]        ),
                    .AC           ( addr[0]          ),
                    .D            ( wdata            ),
                    .BW           ( bw               ),
                    .Q            ( rdata            ),
                    .T_LOGIC      ( 1'b0             ),
                    .MA_SAWL      ( '0               ),
                    .MA_WL        ( '0               ),
                    .MA_WRAS      ( '0               ),
                    .MA_WRASD     ( '0               ),
                    .OBSV_CTL     (                  )

                );

            end

            6: begin
                logic          n_as;
                logic [2:0]    n_aw;
                logic [1:0]    n_ac;
                logic [127:0]   bw;
                assign {n_aw[2], n_as, n_aw[1:0], n_ac} = addr;
                assign bw = (we_n) ?  '0 : '1;

                IN22FDX_R1PH_NFHN_W00064B128M02C256 sram_data // /usr/pack/gf-22-kgf/dz/mem/R1PH/V03R01/model/verilog/
                (

                    .CLK          ( clk              ),
                    .CEN          ( cs_n             ),
                    .RDWEN        ( write            ),
                    .AW           ( addr[5:1]        ),
                    .AC           ( addr[0]          ),
                    .D            ( wdata            ),
                    .BW           ( bw               ),
                    .Q            ( rdata            ),
                    .T_LOGIC      ( 1'b0             ),
                    .MA_SAWL      ( '0               ),
                    .MA_WL        ( '0               ),
                    .MA_WRAS      ( '0               ),
                    .MA_WRASD     ( '0               ),
                    .OBSV_CTL     (                  )

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
