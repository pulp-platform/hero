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

    logic [data_width-1:0] wdata_int;
    assign {>>{wdata_int}} = wdata;

    sram #(
      .DATA_WIDTH (data_width),
      .N_WORDS    (1 << addr_width)
    ) i_sram (
      // DFT
      .mem_ctrl,
      .dft_ram_gt_se,
      .dft_ram_bypass,
      .dft_ram_bp_clk_en,

      .clk_i    (clk),
      .rst_ni   (rst_n),
      .req_i    (req),
      .we_i     (write),
      .addr_i   (addr),
      .wdata_i  (wdata_int),
      .be_i     (be),
      .rdata_o  (rdata)
    );

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
