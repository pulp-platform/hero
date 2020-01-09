// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module hw_barrier_unit
#(
  parameter NB_CORES = 4
)
(
  // clock and reset
  input  logic clk_i,
  input  logic rst_ni,

  // trigger inputs from all cores
  input  logic [NB_CORES-1:0] barrier_trigger_core_i,
  // direct output of status reg for summary status computation in top level
  output logic [NB_CORES-1:0] barrier_status_o,
  // generated event, masked with target core mask -> to eu_core
  output logic [NB_CORES-1:0] barrier_events_o,

  // demuxed slave ports from each core, reduced to one bus
  XBAR_PERIPH_BUS.Slave     demux_bus_slave,
  // single plug from periph interconnect with pre-decoded requests
  XBAR_PERIPH_BUS.Slave     periph_bus_slave

 );

    // actual registers
    logic      [NB_CORES-1:0] trigger_mask_DP;
    logic      [NB_CORES-1:0] target_mask_DP;
    logic      [NB_CORES-1:0] trigger_status_DP;

    logic [2:0][NB_CORES-1:0] trigger_matrix;          // first row for demuxed ports, then interc, then core_trigger
    logic [NB_CORES-1:0][2:0] trigger_matrix_transp;
    logic      [NB_CORES-1:0] trigger_matrix_red;

    logic  demux_we_trigger_mask, demux_we_target_mask;
    logic  interc_we_trigger_mask, interc_we_target_mask;

    // delayed read requests
    logic     [1:0] demux_read_req_del_SP, demux_read_req_del_SN;
    logic     [1:0] interc_read_req_del_SP, interc_read_req_del_SN;

    logic interc_gnt_del_SP, interc_gnt_del_SN;
    logic write_conflict;

    logic barrier_matched;

    genvar I,J;

    // calculation of outputs
    assign barrier_status_o = trigger_status_DP;
    assign barrier_matched  = (trigger_mask_DP != '0) && (trigger_status_DP == trigger_mask_DP);
    assign barrier_events_o = barrier_matched ? target_mask_DP : '0;


    // read/write logic for demuxed ports
    always_comb begin
      demux_we_trigger_mask   = 1'b0;
      demux_we_target_mask    = 1'b0;
      demux_read_req_del_SN   = 2'b00;

      demux_bus_slave.r_rdata = '0;
      demux_bus_slave.r_opc   = 1'b0;
      demux_bus_slave.r_id    = '0;
      demux_bus_slave.gnt     = 1'b1;
      demux_bus_slave.r_valid = 1'b1;

      trigger_matrix[0]       = '0;

      if ( demux_bus_slave.req == 1'b1 ) begin
        if ( demux_bus_slave.wen == 1'b1 ) begin
          // minimal encoding of requested read data
          case ( demux_bus_slave.add[4:2] )
            3'b000: demux_read_req_del_SN = 2'b01;
            3'b001: demux_read_req_del_SN = 2'b10;
            3'b011: demux_read_req_del_SN = 2'b11;
          endcase
        end
        else begin
          case ( demux_bus_slave.add[4:2] )
            3'b000: demux_we_trigger_mask = 1'b1;
            3'b011: demux_we_target_mask  = 1'b1;
            3'b100: trigger_matrix[0]     = demux_bus_slave.wdata[NB_CORES-1:0];
          endcase
        end
      end
      // evaluate delayed read request
      case ( demux_read_req_del_SP )
        2'b01: demux_bus_slave.r_rdata[NB_CORES-1:0] = trigger_mask_DP;
        2'b10: demux_bus_slave.r_rdata[NB_CORES-1:0] = trigger_status_DP;
        2'b11: demux_bus_slave.r_rdata[NB_CORES-1:0] = target_mask_DP;
      endcase
    end

    // detect write collision between demuxed and pe interconnect port
    assign write_conflict = ( (demux_bus_slave.req == 1'b1) && (periph_bus_slave.req == 1'b1) )  &&
                            ( (demux_bus_slave.wen == 1'b0) && (periph_bus_slave.wen == 1'b0) );
                               // simplified condition, should've little to no performance impact       &&
                               //(  demux_bus_slaves[I].add == periph_bus_slave.add );

    // protocol logic for interconnect port - stall interconnect port on write conflict
    assign interc_gnt_del_SN        = periph_bus_slave.req & ~write_conflict;
    assign periph_bus_slave.gnt     = interc_gnt_del_SN;
    assign periph_bus_slave.r_valid = interc_gnt_del_SP;
    assign periph_bus_slave.r_opc   = 1'b0;
    assign periph_bus_slave.r_id    = '0;

    // read/write logic for interconnect port
    always_comb begin
      interc_we_trigger_mask      = 1'b0;
      interc_we_target_mask       = 1'b0;
      interc_read_req_del_SN      = 2'b0;
      periph_bus_slave.r_rdata    = '0;
      trigger_matrix[1]           = '0;

      if ( periph_bus_slave.req == 1'b1 ) begin
        if ( periph_bus_slave.wen == 1'b1 ) begin
          case ( periph_bus_slave.add[4:2] )
            3'b000: interc_read_req_del_SN = 2'b01;
            3'b001: interc_read_req_del_SN = 2'b10;
            3'b011: interc_read_req_del_SN = 2'b11;
          endcase
        end
        else begin
          case ( periph_bus_slave.add[4:2] )
            3'b000: interc_we_trigger_mask   = 1'b1;
            3'b011: interc_we_target_mask    = 1'b1;
            3'b100: trigger_matrix[1]        = periph_bus_slave.wdata[NB_CORES-1:0];
          endcase
        end
      end
      // evaluate delayed read request
      case ( interc_read_req_del_SP )
        2'b01: periph_bus_slave.r_rdata[NB_CORES-1:0] = trigger_mask_DP;
        2'b10: periph_bus_slave.r_rdata[NB_CORES-1:0] = trigger_status_DP;
        2'b11: periph_bus_slave.r_rdata[NB_CORES-1:0] = target_mask_DP;
      endcase
    end

    // combination of all trigger signals and status clear logic
    assign trigger_matrix[2] = barrier_trigger_core_i;
    generate
      for ( I = 0; I < NB_CORES; I++ ) begin
        for ( J = 0; J < 3; J++ ) assign trigger_matrix_transp[I][J] = trigger_matrix[J][I];
        assign trigger_matrix_red[I] = |trigger_matrix_transp[I];
      end
    endgenerate

    always_ff @(posedge clk_i, negedge rst_ni) begin
      if ( rst_ni == 1'b0 ) begin
        trigger_mask_DP         <= '0;
        target_mask_DP          <= '0;
        trigger_status_DP       <= '0;
        demux_read_req_del_SP   <= '0;
        interc_read_req_del_SP  <= '0;
        interc_gnt_del_SP       <= '0;
      end
      else begin

        // summarization of write data for trigger and target masks
        if ( demux_we_trigger_mask )
          trigger_mask_DP <= demux_bus_slave.wdata[NB_CORES-1:0];
        else if ( interc_we_trigger_mask == 1'b1 )
          trigger_mask_DP <= periph_bus_slave.wdata[NB_CORES-1:0];

        if ( demux_we_target_mask )
          target_mask_DP  <= demux_bus_slave.wdata[NB_CORES-1:0];
        else if ( interc_we_target_mask == 1'b1 )
          target_mask_DP  <= periph_bus_slave.wdata[NB_CORES-1:0];

        if( barrier_matched )
            trigger_status_DP  <=  '0;
        else if(|trigger_matrix_red)
            trigger_status_DP  <= (trigger_status_DP | trigger_matrix_red);

        if ( demux_bus_slave.req ) begin
          demux_read_req_del_SP   <= demux_read_req_del_SN;
        end
        if ( periph_bus_slave.req ) begin
          interc_read_req_del_SP  <= interc_read_req_del_SN;
          interc_gnt_del_SP       <= interc_gnt_del_SN;
        end
      end
    end

endmodule // hw_barrier_unit
