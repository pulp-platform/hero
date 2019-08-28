// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/*
 * Francesco Conti <f.conti@unibo.it>
 */

module register_file_1r_1w_be
#(
    parameter ADDR_WIDTH    = 5,
    parameter DATA_WIDTH    = 64,
    parameter NUM_BYTE      = DATA_WIDTH/8
)
(
    input   logic                                         clk,
    input   logic                                         rst_n,

    input   logic                                         ReadEnable,
    input   logic [ADDR_WIDTH-1:0]                        ReadAddr,
    output  logic [DATA_WIDTH-1:0]                        ReadData,

    input   logic [ADDR_WIDTH-1:0]                        WriteAddr,
    input   logic                                         WriteEnable,
    input   logic [NUM_BYTE-1:0][DATA_WIDTH/NUM_BYTE-1:0] WriteData,
    input   logic [NUM_BYTE-1:0]                          WriteBE
);

  localparam N_SCM_REGISTERS = 2**ADDR_WIDTH;

  // signals
  (* ram_style = "block" *) logic [N_SCM_REGISTERS-1:0][NUM_BYTE-1:0][DATA_WIDTH/NUM_BYTE-1:0] MemContent_int; // BRAM
  logic [DATA_WIDTH-1:0]                                                                       ReadData_reg;

  // Read Port
  always_ff @(posedge clk or negedge rst_n)
  begin
    if(rst_n == 1'b0)
      ReadData_reg <= '0;
    else if(ReadEnable == 1'b1)
      ReadData_reg <= MemContent_int[ReadAddr];
  end

  always_comb
  begin : register_read_port_behavioral
    ReadData <= ReadData_reg;
  end

  // Write Port
  always_ff @(posedge clk or negedge rst_n)
  begin
    if(rst_n == 1'b0) begin
      MemContent_int <= '0;
    end
    else if(WriteEnable == 1'b1) begin
      for(int i=0; i<NUM_BYTE; i++)
        if(WriteBE[i] == 1'b1)
          MemContent_int[WriteAddr][i] <= WriteData[i];
    end
  end

endmodule