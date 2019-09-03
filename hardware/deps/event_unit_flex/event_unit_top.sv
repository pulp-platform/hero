// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module event_unit_top
#(
  parameter NB_CORES = 8,
  parameter NB_SW_EVT = 8,
  parameter NB_BARR  = 8,
  parameter NB_HW_MUT = 1,
  parameter MUTEX_MSG_W = 32,
  parameter DISP_FIFO_DEPTH = 8,
  parameter PER_ID_WIDTH = 9,
  parameter EVNT_WIDTH = 8,
  parameter SOC_FIFO_DEPTH = 8
)
(
  // clock and reset
  input  logic  clk_i,
  input  logic  rst_ni,
  input  logic  test_mode_i,

  // all kinds of cluster internal events, split into different signals for readability
  input  logic [NB_CORES-1:0][3:0]  acc_events_i,
  input  logic [NB_CORES-1:0][1:0]  dma_events_i,
  input  logic [NB_CORES-1:0][1:0]  timer_events_i,
  // usually much less than 32 bit, only for flexibility for different chips
  input  logic [NB_CORES-1:0][31:0] cluster_events_i,

  output logic [NB_CORES-1:0]       core_irq_req_o,
  output logic [NB_CORES-1:0][4:0]  core_irq_id_o,
  input  logic [NB_CORES-1:0]       core_irq_ack_i,
  input  logic [NB_CORES-1:0][4:0]  core_irq_ack_id_i,

  input  logic [NB_CORES-1:0]       core_busy_i,
  output logic [NB_CORES-1:0]       core_clock_en_o,

  // bus slave connections - periph bus and eu_direct_link
  XBAR_PERIPH_BUS.Slave     speriph_slave,
  XBAR_PERIPH_BUS.Slave     eu_direct_link[NB_CORES-1:0],

  // soc periph events
  input  logic                  soc_periph_evt_valid_i,
  output logic                  soc_periph_evt_ready_o,
  input  logic [EVNT_WIDTH-1:0] soc_periph_evt_data_i,

  // message bus connections - dummy implementation
  MESSAGE_BUS.Master        message_master

 );

    // event lines from soc periph fifo and inter-cluster event dispatch
    logic soc_periph_event;

    // sw events and target core mask from each core
    logic [NB_SW_EVT-1:0][NB_CORES-1:0] core_sw_events;
    logic [NB_CORES-1:0][NB_SW_EVT-1:0] core_sw_events_transp;
    logic [NB_CORES-1:0][NB_CORES-1:0]  core_sw_events_mask;
    logic [NB_CORES-1:0][NB_CORES-1:0]  core_sw_events_mask_transp;
    logic [NB_CORES-1:0][7:0]           sw_events_combined;
    // sw events from interconnect
    logic [NB_CORES-1:0][NB_SW_EVT-1:0] interc_int_events_sw;


    // cluster internal event matrix: sw, barr and other cluster events
    logic [NB_CORES-1:0][31:0]          cluster_int_events;

    // link between hw barrier and eu core units to fast trigger barriers
    logic [NB_CORES-1:0][NB_BARR-1:0]   hw_barr_trigger;
    logic [NB_BARR-1:0][NB_CORES-1:0]   hw_barr_trigger_transp;

    // intermediate signals for assigning
    logic [NB_CORES-1:0][NB_SW_EVT-1:0] cluster_int_events_sw;
    logic [NB_CORES-1:0][NB_BARR-1:0]   cluster_int_events_barr;
    logic [NB_BARR-1:0][NB_CORES-1:0]   cluster_int_events_barr_transp;
    logic [NB_CORES-1:0]                cluster_int_events_barr_red;
    logic [NB_CORES-1:0][NB_HW_MUT-1:0] cluster_int_events_mutex;
    logic [NB_HW_MUT-1:0][NB_CORES-1:0] cluster_int_events_mutex_transp;
    logic [NB_CORES-1:0]                cluster_int_events_mutex_red;
    logic [NB_CORES-1:0]                cluster_int_events_dispatch;

    // hw mutex related signals
    logic [NB_CORES-1:0][NB_HW_MUT-1:0] mutex_lock_req;
    logic [NB_HW_MUT-1:0][NB_CORES-1:0] mutex_lock_req_transp;
    logic [NB_CORES-1:0][NB_HW_MUT-1:0] mutex_unlock_req;
    logic [NB_HW_MUT-1:0][NB_CORES-1:0] mutex_unlock_req_transp;

    logic [NB_HW_MUT-1:0][MUTEX_MSG_W-1:0]               mutex_msg_rdata;
    logic [NB_CORES-1:0][NB_HW_MUT-1:0][MUTEX_MSG_W-1:0] mutex_msg_wdata;
    logic [NB_HW_MUT-1:0][MUTEX_MSG_W-1:0][NB_CORES-1:0] mutex_msg_wdata_transp;
    logic [NB_HW_MUT-1:0][MUTEX_MSG_W-1:0]               mutex_msg_wdata_transp_red;

    // hw dispatch related signals
    logic [NB_CORES-1:0]       disp_pop_req;
    logic [NB_CORES-1:0]       disp_pop_ack;
    logic [NB_CORES-1:0][31:0] disp_value;

    logic [NB_CORES-1:0]       disp_w_req;
    logic [NB_CORES-1:0][31:0] disp_w_data;
    logic [NB_CORES-1:0][1:0]  disp_reg_sel;

    // periph bus links to all subcomponents
    XBAR_PERIPH_BUS periph_int_bus[NB_CORES+NB_BARR+2:0]();

    // demux periph bus to eu_core and barrier units
    XBAR_PERIPH_BUS demux_int_bus_core[NB_CORES-1:0]();
    XBAR_PERIPH_BUS demux_int_bus_barrier[NB_CORES*NB_BARR-1:0]();

    genvar I,J,K;

    // combination of trigger sources for sw events
    generate
      for ( I = 0; I < NB_CORES; I++ ) begin : SW_EVENTS_COMBINE
        always_comb begin
          sw_events_combined[I][7:0]           = '0;
          sw_events_combined[I][NB_SW_EVT-1:0] = cluster_int_events_sw[I] | interc_int_events_sw[I];
        end
      end
    endgenerate

    cluster_event_map #(
      .NB_CORES  ( NB_CORES ) )
    cluster_event_map_i (
      .sw_events_i         ( sw_events_combined           ),
      .barrier_events_i    ( cluster_int_events_barr_red  ),
      .mutex_events_i      ( cluster_int_events_mutex_red ),
      .dispatch_events_i   ( cluster_int_events_dispatch  ),
      .periph_fifo_event_i ( soc_periph_event             ),

      .acc_events_i        ( acc_events_i       ),
      .dma_events_i        ( dma_events_i       ),
      .timer_events_i      ( timer_events_i     ),
      .cluster_events_i    ( cluster_events_i   ),

      .events_mapped_o     ( cluster_int_events )
    );

    // combinational calculation of every sw event line for every core
    // transposing and combinational reduction of barrier and mutex events and signals
    generate
      for ( I=0; I < NB_CORES; I++ ) begin : EU_LOOP_CORE
        assign cluster_int_events_barr_red[I]  = |cluster_int_events_barr[I];
        assign cluster_int_events_mutex_red[I] = |cluster_int_events_mutex[I];

        for ( J=0; J < NB_BARR; J++ ) begin : EU_LOOP_HW_BARR_TRANSP
          assign hw_barr_trigger_transp[J][I]  = hw_barr_trigger[I][J];
          assign cluster_int_events_barr[I][J] = cluster_int_events_barr_transp[J][I];
        end

        for ( J=0; J < NB_SW_EVT; J++ ) begin : EU_LOOP_SW_EVTS_TRANSP
          assign core_sw_events[J][I]        = core_sw_events_transp[I][J];
        end
          
        for ( J=0; J < NB_CORES; J++ ) begin : EU_LOOP_SW_EVTS_MASK_TRANSP
          assign core_sw_events_mask[J][I]   = core_sw_events_mask_transp[I][J];
        end

        for ( J=0; J < NB_SW_EVT; J++ ) begin : EU_LOOP_SW_EVTS_MASK_APPLY
          assign cluster_int_events_sw[I][J] = (core_sw_events[J][NB_CORES-1:0] & core_sw_events_mask[I][NB_CORES-1:0]) != '0;
        end

        for ( J=0; J < NB_HW_MUT; J++ ) begin : EU_LOOP_HW_MUTEX_TRANSP
          assign cluster_int_events_mutex[I][J] = cluster_int_events_mutex_transp[J][I];
          assign mutex_lock_req_transp[J][I]    = mutex_lock_req[I][J];
          assign mutex_unlock_req_transp[J][I]  = mutex_unlock_req[I][J];
          for ( K=0; K < MUTEX_MSG_W; K++ ) begin : EU_LOOP_HW_MUTEX_TRANSP_MSG
            assign mutex_msg_wdata_transp[J][K][I]  = mutex_msg_wdata[I][J][K];
          end
        end
      end

      for ( J=0; J < NB_HW_MUT; J++ ) begin : EU_LOOP_HW_MUTEX_REDUCE_STG1
        for ( K=0; K < MUTEX_MSG_W; K++ ) begin : EU_LOOP_HW_MUTEX_REDUCE_STG2
          assign mutex_msg_wdata_transp_red[J][K] = |mutex_msg_wdata_transp[J][K];
        end
      end
    endgenerate

    // dummy assignments
    assign periph_int_bus[NB_CORES+NB_BARR+2].gnt     = 1'b0;
    assign periph_int_bus[NB_CORES+NB_BARR+2].r_opc   = 1'b0;
    assign periph_int_bus[NB_CORES+NB_BARR+2].r_valid = 1'b0;
    assign periph_int_bus[NB_CORES+NB_BARR+2].r_rdata = '0;
    assign periph_int_bus[NB_CORES+NB_BARR+2].r_id    = '0;

    // will become the master port for cluster messages
    assign message_master.wdata = '0;
    assign message_master.req   = 1'b0;
    assign message_master.wen   = 1'b1;
    assign message_master.add   = '0;
    assign message_master.be    = '0;
    assign message_master.id    = '0;


    event_unit_interface_mux #(
      .NB_CORES ( NB_CORES ),
      .NB_BARR  ( NB_BARR  ) )
    event_unit_interface_mux_i (
      .clk_i                        ( clk_i                 ),
      .rst_ni                       ( rst_ni                ),

      .speriph_slave                ( speriph_slave         ),
      .periph_int_bus_master        ( periph_int_bus        ),

      .demux_slave                  ( eu_direct_link        ),
      .demux_int_bus_core_master    ( demux_int_bus_core    ),
      .demux_int_bus_barrier_master ( demux_int_bus_barrier )
    );


    interc_sw_evt_trig #(
      .NB_CORES  ( NB_CORES  ),
      .NB_SW_EVT ( NB_SW_EVT ) )
    interc_sw_evt_trig_i (
      .clk_i                ( clk_i                            ),
      .rst_ni               ( rst_ni                           ),

      .sw_events_o          ( interc_int_events_sw             ),

      .periph_int_bus_slave ( periph_int_bus[NB_CORES+NB_BARR] )
    );


    soc_periph_fifo #(
      .ID_WIDTH   ( EVNT_WIDTH ),
      .FIFO_DEPTH ( SOC_FIFO_DEPTH ) )
    soc_periph_fifo_i (
      .clk_i                ( clk_i                              ),
      .rst_ni               ( rst_ni                             ),

      .incoming_evt_o       ( soc_periph_event                   ),

      .fifo_data_valid_i    ( soc_periph_evt_valid_i             ),
      .fifo_fulln_o         ( soc_periph_evt_ready_o             ),
      .fifo_data_i          ( soc_periph_evt_data_i              ),

      .periph_int_bus_slave ( periph_int_bus[NB_CORES+NB_BARR+1] )
    );


    generate
      for ( I=0; I < NB_CORES; I++ ) begin : EU_CORE
        event_unit_core #(
          .NB_CORES    ( NB_CORES    ),
          .NB_SW_EVT   ( NB_SW_EVT   ),
          .NB_BARR     ( NB_BARR     ),
          .NB_HW_MUT   ( NB_HW_MUT   ), 
          .MUTEX_MSG_W ( MUTEX_MSG_W ) )
        event_unit_core_i (
          .clk_i                 ( clk_i                                         ),
          .rst_ni                ( rst_ni                                        ),
          .test_mode_i           ( test_mode_i                                   ),
  
          .master_event_lines_i  ( cluster_int_events[I]                         ),
  
          .core_sw_events_o      ( core_sw_events_transp[I][NB_SW_EVT-1:0]       ),
          .core_sw_events_mask_o ( core_sw_events_mask_transp[I][NB_CORES-1:0]   ),
  
          .hw_barr_id_o          ( hw_barr_trigger[I][NB_BARR-1:0]               ),

          .mutex_rd_req_o        ( mutex_lock_req[I]                             ),
          .mutex_wr_req_o        ( mutex_unlock_req[I]                           ),
          .mutex_msg_wdata_o     ( mutex_msg_wdata[I]                            ),
          .mutex_msg_rdata_i     ( mutex_msg_rdata                               ),

          .dispatch_pop_req_o    ( disp_pop_req[I]                               ),
          .dispatch_pop_ack_o    ( disp_pop_ack[I]                               ),
          .dispatch_value_i      ( disp_value[I]                                 ),

          .dispatch_w_req_o      ( disp_w_req[I]                                 ),
          .dispatch_w_data_o     ( disp_w_data[I]                                ),
          .dispatch_reg_sel_o    ( disp_reg_sel[I]                               ),

          .core_irq_req_o        ( core_irq_req_o[I]                             ),
          .core_irq_id_o         ( core_irq_id_o[I]                              ),
          .core_irq_ack_i        ( core_irq_ack_i[I]                             ),
          .core_irq_ack_id_i     ( core_irq_ack_id_i[I]                          ),

          .core_busy_i           ( core_busy_i[I]                                ),
          .core_clock_en_o       ( core_clock_en_o[I]                            ),
  
          .periph_int_bus_slave  ( periph_int_bus[I]                             ),
          .eu_direct_link_slave  ( demux_int_bus_core[I]                         )
        );
      end
    endgenerate


    // instantiation of NB_BARR barrier units
    generate
      for ( I = 0; I < NB_BARR; I++ ) begin : HW_BARRIER_UNIT
        hw_barrier_unit #(
          .NB_CORES ( NB_CORES ) )
        hw_barrier_unit_i (
          .clk_i                  ( clk_i                                              ),
          .rst_ni                 ( rst_ni                                             ),

          .barrier_trigger_core_i ( hw_barr_trigger_transp[I]                          ),
          .barrier_status_o       (                                                    ),
          .barrier_events_o       ( cluster_int_events_barr_transp[I]                  ),

          .demux_bus_slaves       ( demux_int_bus_barrier[(I+1)*NB_CORES-1:I*NB_CORES] ),
          .periph_bus_slave       ( periph_int_bus[NB_CORES+I]                         )
        );
      end
    endgenerate


    generate
      for ( I=0; I < NB_HW_MUT; I++ ) begin : HW_MUT
        hw_mutex_unit #(
          .NB_CORES     ( NB_CORES    ),
          .MUTEX_MSG_W  ( MUTEX_MSG_W ) )
        hw_mutex_unit_i (
          .clk_i             ( clk_i                              ),
          .rst_ni            ( rst_ni                             ),
          
          .lock_req_i        ( mutex_lock_req_transp[I]           ),
          .unlock_req_i      ( mutex_unlock_req_transp[I]         ),

          .mutex_msg_wdata_i ( mutex_msg_wdata_transp_red[I]      ),
          .mutex_msg_rdata_o ( mutex_msg_rdata[I]                 ),

          .mutex_event_o     ( cluster_int_events_mutex_transp[I] )
        );
      end
    endgenerate

    hw_dispatch #(
      .NB_CORES   ( NB_CORES ),
      .FIFO_DEPTH ( DISP_FIFO_DEPTH ) )
    hw_dispatch_i (
      .clk_i            ( clk_i                       ),
      .rst_ni           ( rst_ni                      ),

      .pop_req_i        ( disp_pop_req                ),
      .pop_ack_i        ( disp_pop_ack                ),

      .dispatch_value_o ( disp_value                  ),

      .w_req_i          ( disp_w_req                  ),
      .w_data_i         ( disp_w_data                 ),
      .reg_sel_i        ( disp_reg_sel                ),

      .dispatch_event_o ( cluster_int_events_dispatch )
    );

endmodule // event_unit_top
