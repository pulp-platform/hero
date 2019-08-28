// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module interc_sw_evt_trig
#(
  parameter NB_CORES  = 4,
  parameter NB_SW_EVT = 8
)
(
  input  logic clk_i,
  input  logic rst_ni,

  output logic [NB_CORES-1:0][NB_SW_EVT-1:0] sw_events_o,

  // bus to read the oldest event id
  XBAR_PERIPH_BUS.Slave periph_int_bus_slave
);

  logic [NB_SW_EVT-1:0][NB_CORES-1:0] sw_events_transp;

  genvar I,J;

  generate
    for ( I=0; I < NB_CORES; I++ ) begin
      for ( J=0; J < NB_SW_EVT; J++ ) 
        assign sw_events_o[I][J] = sw_events_transp[J][I];
    end
  endgenerate

  // no stall functionality
  assign periph_int_bus_slave.gnt     = periph_int_bus_slave.req;
  assign periph_int_bus_slave.r_rdata = '0;
  assign periph_int_bus_slave.r_id    = '0;
  assign periph_int_bus_slave.r_opc   = 1'b0;

  // trigger logic
  always_comb begin
    
    sw_events_transp = '0;

    if (periph_int_bus_slave.req & ~periph_int_bus_slave.wen) begin
      if (periph_int_bus_slave.wdata == '0)
        sw_events_transp[periph_int_bus_slave.add[4:2]] = '1;
      else
        sw_events_transp[periph_int_bus_slave.add[4:2]] = periph_int_bus_slave.wdata[NB_CORES-1:0];
    end

  end

  // register setup
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if( rst_ni == 1'b0 )
      periph_int_bus_slave.r_valid <= 1'b0;
    else
      periph_int_bus_slave.r_valid <= periph_int_bus_slave.req;
  end

endmodule
