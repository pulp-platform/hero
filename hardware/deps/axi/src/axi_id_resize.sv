// Copyright (c) 2014-2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Andreas Kurth <akurth@iis.ee.ethz.ch>
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// Change the AXI ID width.
///
/// This module instantiates a remapper if the outgoing ID is smaller than the incoming ID.
/// Otherwise, it instantiates a joiner, which implicitly expands AXI IDs.
module axi_id_resize #(
  parameter int unsigned ADDR_WIDTH   = 0,
  parameter int unsigned DATA_WIDTH   = 0,
  parameter int unsigned USER_WIDTH   = 0,
  parameter int unsigned ID_WIDTH_IN  = 0,
  parameter int unsigned ID_WIDTH_OUT = 0,
  parameter int unsigned TABLE_SIZE   = 0
) (
  input logic     clk_i,
  input logic     rst_ni,
  AXI_BUS.Slave   in,
  AXI_BUS.Master  out
);
  if (ID_WIDTH_OUT < ID_WIDTH_IN) begin : gen_remap
    axi_id_remap #(
      .ADDR_WIDTH   ( ADDR_WIDTH   ),
      .DATA_WIDTH   ( DATA_WIDTH   ),
      .USER_WIDTH   ( USER_WIDTH   ),
      .ID_WIDTH_IN  ( ID_WIDTH_IN  ),
      .ID_WIDTH_OUT ( ID_WIDTH_OUT ),
      .TABLE_SIZE   ( TABLE_SIZE   )
    ) i_remap (
      .clk_i  ( clk_i  ),
      .rst_ni ( rst_ni ),
      .in     ( in     ),
      .out    ( out    )
    );
  end else begin : gen_join
    axi_join_intf i_join (in, out);
  end

endmodule
