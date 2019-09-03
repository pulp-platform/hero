// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module hw_dispatch
#(
  parameter NB_CORES = 4,
  parameter FIFO_DEPTH = 4
)
(
  // clock and reset
  input  logic clk_i,
  input  logic rst_ni,

  // pop request and ack from each core
  input  logic [NB_CORES-1:0] pop_req_i,
  input  logic [NB_CORES-1:0] pop_ack_i,
  // current read data for each core
  output logic [NB_CORES-1:0][31:0] dispatch_value_o,

  // value push and team configuration by master
  input  logic [NB_CORES-1:0]       w_req_i,
  input  logic [NB_CORES-1:0][31:0] w_data_i,
  input  logic [NB_CORES-1:0][1:0]  reg_sel_i,

  // event output to flag availability of a value to a specific core
  output logic [NB_CORES-1:0] dispatch_event_o

);

  // registers
  logic [FIFO_DEPTH-1:0][31:0] dispatch_fifo_DP, dispatch_fifo_DN;

  logic [NB_CORES-1:0] core_set_conf_DP, core_set_conf_DN;
  logic [NB_CORES-1:0] req_in_progr_SP, req_in_progr_SN;
  logic [NB_CORES-1:0] incr_rptr_del_SP, incr_rptr_del_SN;

  logic [FIFO_DEPTH-1:0][NB_CORES-1:0] core_set_stat_DP, core_set_stat_DN;

  logic [NB_CORES-1:0][$clog2(FIFO_DEPTH)-1:0] read_ptr_DP, read_ptr_DN;
  logic [$clog2(FIFO_DEPTH)-1:0]               write_ptr_DP, write_ptr_DN;

  // internal signals
  logic [NB_CORES-1:0][1:0][31:0] w_data_int;
  logic [1:0][31:0][NB_CORES-1:0] w_data_int_transp;
  logic [1:0][31:0]               w_data_int_red;
  logic [1:0][NB_CORES-1:0]       w_req_int;

  logic [NB_CORES-1:0][FIFO_DEPTH-1:0] clr_core_stat;
  logic [FIFO_DEPTH-1:0][NB_CORES-1:0] clr_core_stat_transp;

  genvar I,J,K;

  // workaround for language limitation
  generate
    for (I=0; I<NB_CORES; I++) begin
      for (J=0; J<FIFO_DEPTH; J++) assign clr_core_stat_transp[J][I] = clr_core_stat[I][J];
    end
  endgenerate

  // combinational reduction of write data
  generate
    for (J=0; J<2; J++) begin
      for (I=0; I<NB_CORES; I++) begin
        assign w_req_int[J][I]  = ( w_req_i[I] && (reg_sel_i[I] == J) );
        assign w_data_int[I][J] = ( w_req_int[J][I] ) ? w_data_i[I] : '0;
        for (K=0; K<32; K++)
          assign w_data_int_transp[J][K][I] = w_data_int[I][J][K];
      end
      for (K=0; K<32; K++)
        assign w_data_int_red[J][K] = |w_data_int_transp[J][K];
    end
  endgenerate

  generate 
    for (I=0; I<NB_CORES; I++) begin
      assign dispatch_value_o[I] = dispatch_fifo_DP[read_ptr_DP[I]];

      // read pointer management
      always_comb begin
        dispatch_event_o[I] = 1'b0;
        clr_core_stat[I]    = '0;

        req_in_progr_SN[I]  = req_in_progr_SP[I];
        read_ptr_DN[I]      = read_ptr_DP[I];
        incr_rptr_del_SN[I] = 1'b0;

        // check for and register incoming requests
        if ( pop_req_i[I] | req_in_progr_SP[I] ) begin
          req_in_progr_SN[I] = 1'b1;
          // notify core through event if there is a valid value for it
          if ( core_set_stat_DP[read_ptr_DP[I]][I] ) begin
            dispatch_event_o[I] = 1'b1;
          end
          // request but no valid value: increase read pointer till write point
          else begin
            if ( read_ptr_DP[I] != write_ptr_DP )
              read_ptr_DN[I] = (read_ptr_DP[I] + 1) % FIFO_DEPTH;
          end
        end

        // handle the case where a dispatch value has been successfully read
        if ( req_in_progr_SP[I] &  pop_ack_i[I] ) begin
          req_in_progr_SN[I]  = 1'b0;
          incr_rptr_del_SN[I] = 1'b1;

          clr_core_stat[I][read_ptr_DP[I]] = 1'b1;
        end

        // event_unit_core needs one more cycle to get the correct value
        if ( incr_rptr_del_SP[I] ) read_ptr_DN[I] = (read_ptr_DP[I] + 1) % FIFO_DEPTH;

      end

    end
  endgenerate

  // write process
  always_comb begin
    // prepared configuration
    core_set_conf_DN  = core_set_conf_DP;
    
    // will be written upon a push
    write_ptr_DN      = write_ptr_DP;
    dispatch_fifo_DN  = dispatch_fifo_DP;
    core_set_stat_DN  = core_set_stat_DP & ~clr_core_stat_transp;

    if ( |w_req_int[0] ) begin
      // write value into FIFO and copy prepared configuration
      dispatch_fifo_DN[write_ptr_DP]  = w_data_int_red[0];
      core_set_stat_DN[write_ptr_DP]  = core_set_conf_DP;
      // increment write ptr - no overflow management
      write_ptr_DN = (write_ptr_DP + 1) % FIFO_DEPTH;
    end

    // write the prepared configuration
    if ( |w_req_int[1] ) core_set_conf_DN = w_data_int_red[1][NB_CORES-1:0];

  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if ( rst_ni == 1'b0 ) begin
      dispatch_fifo_DP  <= '0;
      core_set_conf_DP  <= '0;
      req_in_progr_SP   <= '0;
      incr_rptr_del_SP  <= '0;
      core_set_stat_DP  <= '0;
      read_ptr_DP       <= '0;
      write_ptr_DP      <= '0;
    end
    else begin
      if ( |w_req_int[0] )
        dispatch_fifo_DP[write_ptr_DP] <= w_data_int_red[0];

      if ( |w_req_int[1] ) 
        core_set_conf_DP <= w_data_int_red[1][NB_CORES-1:0];

      for (int unsigned index=0; index<NB_CORES; index++) begin
        if ( req_in_progr_SP[index] &  pop_ack_i[index] )
          incr_rptr_del_SP[index] <= 1'b1;
        else
          incr_rptr_del_SP[index] <= 1'b0;
      end

      req_in_progr_SP  <= req_in_progr_SN;

      core_set_stat_DP <= core_set_stat_DN;
      read_ptr_DP      <= read_ptr_DN;
      write_ptr_DP     <= write_ptr_DN;
    end
  end

endmodule // hw_dispatch
