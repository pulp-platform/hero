// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Company:        Institute of Integrated Systems // ETH Zurich              //
//                                                                            //
// Engineer:       Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                                                                            //
// Additional contributions by:                                               //
//                 Roberto Roncone                                            //
//                                                                            //
// Create Date:    12/03/2015                                                 //
// Design Name:    event_unit                                                 //
// Module Name:    event_unit                                                 //
// Project Name:   PULP                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Event unit                                                 //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
//          v0.2 - Major redesign by Roberto Roncone                          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
`include "old_event_unit_defines.sv"

module event_unit
#(
    parameter NUM_CORES=4
)
(
    input logic                        clk_i,
    input logic                        rst_ni,
    input logic[23:0]                  cluster_events_i,
    input logic[7:0]                   ext_events_i,
    input logic[NUM_CORES-1:0]         ready_to_shutdown_i,
    output logic[NUM_CORES-1:0]        IRQ_o,
    output logic[NUM_CORES-1:0]        NMIRQ_o,
    output logic[NUM_CORES-1:0]        fetch_en_o,

    XBAR_PERIPH_BUS.Slave              speriph_slave,
`ifdef FEATURE_DEMUX_MAPPED
    XBAR_PERIPH_BUS.Slave              event_unit_slave[NUM_CORES-1:0],
`endif
    BBMUX_CONFIG_BUS.Master            bbmux_bus,
    CLKGATE_CONFIG_BUS.Master          clkgate_bus
);


   logic [NUM_CORES-1:0]               r_event_detect_link;
   logic [NUM_CORES-1:0]               s_fetch_en_link;
   logic [NUM_CORES-1:0]               clk_gate_core_link;
   logic [7:0]                         r_ext_event;
   logic [7:0]                         r_ext_event_synched;
   logic [15:0]                        dma_events;
   logic [1:0]                         hwce_events;
   logic [`GP_EVNT:0][NUM_CORES-1:0]   s_internal_event_link; // 3 GP + 1 barrier
   logic [NUM_CORES-1:0]               s_barrier_event_link;
   genvar                              i;

   logic [NUM_CORES-1:0]               s_clk_stop_link;
   logic [NUM_CORES-1:0][63:0]         evnt_buffer_clear_link;
   logic [NUM_CORES-1:0][63:0]         interrupt_buffer_clear_link;

`ifdef FEATURE_DEMUX_MAPPED
   generate
     for( i = 0 ; i < NUM_CORES; i++ )
     begin
       assign event_unit_slave[i].r_rdata = '0;
       assign event_unit_slave[i].r_opc   = 1'b0;
       assign event_unit_slave[i].gnt     = event_unit_slave[i].req;

       always_ff @(posedge clk_i, negedge rst_ni)
       begin
         if(rst_ni == 1'b0)
         begin
           event_unit_slave[i].r_valid <= 1'b0;
         end
         else
         begin
           event_unit_slave[i].r_valid <= event_unit_slave[i].req;
         end
       end

       always @(*)
       begin
         s_clk_stop_link[i]             = 1'b0;
         evnt_buffer_clear_link[i]      = '0;
         interrupt_buffer_clear_link[i] = '0;

         if( event_unit_slave[i].req == 1'b1 )
         begin
           case({event_unit_slave[i].add[3:0],event_unit_slave[i].wen})
             5'b0000_0:
             begin
               s_clk_stop_link[i] = event_unit_slave[i].wdata[0];
             end

             5'b0100_0:
             begin
               evnt_buffer_clear_link[i][31:0] = event_unit_slave[i].wdata;
             end

             5'b1000_0:
             begin
               interrupt_buffer_clear_link[i][31:0] = event_unit_slave[i].wdata;
             end

             default:
             begin
             end
           endcase
         end
       end
     end
   endgenerate
`endif



    assign dma_events  = { {(16-NUM_CORES){1'b0}}, cluster_events_i[NUM_CORES+4-1:4]  };
    assign hwce_events = cluster_events_i[21:20];

    //**********************************************************
    //*************** EVENT SYNC  ****************************
    //**********************************************************
    always_ff @(posedge clk_i, negedge rst_ni)
      begin
          if (rst_ni == 1'b0)
            begin
                    r_ext_event <= 'b0;
                    r_ext_event_synched <= 'b0;
            end
          else
            begin
                    r_ext_event <= ext_events_i;
                    r_ext_event_synched <= r_ext_event;
            end
      end


   //********************************************************
   //************** CLKGATE & BBMUX UNIT ********************
   //********************************************************
   logic [NUM_CORES-1:0][31:0]         event_buffer_status_low_link;
   logic [NUM_CORES-1:0][31:0]         event_buffer_status_high_link;
   logic [NUM_CORES-1:0][63:0]         r_evnt_mask_reg_link;
   logic [NUM_CORES-1:0][63:0]         s_evnt_mask_link;
   logic [NUM_CORES-1:0][1:0]          evnt_mask_sel_link;

   logic [NUM_CORES-1:0]               Emergency_clear_evnt_link;
   logic [NUM_CORES-1:0]               Emergency_evnt_status_link;
   logic [NUM_CORES-1:0]               s_emergency_event_link;

   logic [NUM_CORES-1:0][31:0]         interrupt_buffer_status_low_link;
   logic [NUM_CORES-1:0][31:0]         interrupt_buffer_status_high_link;
   logic [NUM_CORES-1:0][63:0]         r_interrupt_mask_reg_link;
   logic [NUM_CORES-1:0][63:0]         s_interrupt_mask_link;
   logic [NUM_CORES-1:0][1:0]          interrupt_mask_sel_link;
   logic [NUM_CORES-1:0]               Emergency_clear_interrupt_link;
   logic [NUM_CORES-1:0]               Emergency_IRQ_status_link;

   logic [NUM_CORES-1:0]               IRQ_link;
   logic [NUM_CORES-1:0]               NMIRQ_link;
   logic [NUM_CORES-1:0]               s_emergency_IRQ_link;
   logic [NUM_CORES-1:0]               core_status;

   logic [NUM_CORES-1:0]               s_IRQ_or_NMIRQ;

   //logic [NUM_CORES-1:0]                        l_barrier_status;
   logic [`NUM_BARRIERS-1:0][$clog2(NUM_CORES):0] barrier_team_num_threads_link;
   logic [`NUM_BARRIERS-1:0]                      barrier_store_link;
   logic [NUM_CORES-1:0]                          barrier_event_link;
   logic [`NUM_BARRIERS-1:0]                      barrier_get_link;
   logic [`NUM_BARRIERS-1:0]                      clear_barrier_req_link;
   logic [`NUM_BARRIERS-1:0][$clog2(NUM_CORES):0] barrier_counter_link;
   logic [6:0]                                    r_clkgate_p_link;
   logic [`NUM_BARRIERS-1:0][NUM_CORES-1:0]       mask_to_trigger_link;
   logic [NUM_CORES-1:0][`GP_EVNT-1:0]            s_GP_event;
`ifdef FEATURE_IDLE_CNT
   logic [NUM_CORES-1:0]                          s_clear_cnt_link;
   logic [NUM_CORES-1:0]                          s_start_cnt_link;
   logic [NUM_CORES-1:0][31:0]                    r_cnt_link;
`endif

    assign s_IRQ_or_NMIRQ = IRQ_link | NMIRQ_link;
    event_unit_input
    #(
        .NUM_CORES(NUM_CORES)
    )
    event_unit_input_i
    (
      .clk_i                          ( clk_i                             ),
      .rst_ni                         ( rst_ni                            ),
      .r_event_detect_i               ( r_event_detect_link               ),
      .event_buffer_status_low_i      ( event_buffer_status_low_link      ),
      .event_buffer_status_high_i     ( event_buffer_status_high_link     ),
      .evnt_mask_reg_i                ( r_evnt_mask_reg_link              ),
      .evnt_mask_o                    ( s_evnt_mask_link                  ),
      .evnt_mask_sel_o                ( evnt_mask_sel_link                ),
      `ifndef FEATURE_DEMUX_MAPPED
      .evnt_buffer_clear_o            ( evnt_buffer_clear_link            ),
      .s_clk_stop_o                   ( s_clk_stop_link                   ),
      `endif
      .Emergency_event_o              ( s_emergency_event_link            ),
      .Emergency_evnt_clear_o         ( Emergency_clear_evnt_link         ),
      .Emergency_event_status_i       ( Emergency_evnt_status_link        ),

      .interrupt_buffer_status_low_i  ( interrupt_buffer_status_low_link  ),
      .interrupt_buffer_status_high_i ( interrupt_buffer_status_high_link ),
      .interrupt_mask_reg_i           ( r_interrupt_mask_reg_link         ),
      .interrupt_mask_o               ( s_interrupt_mask_link             ),
      .interrupt_mask_sel_o           ( interrupt_mask_sel_link           ),
      `ifndef FEATURE_DEMUX_MAPPED
      .interrupt_buffer_clear_o       ( interrupt_buffer_clear_link       ),
      `endif
      .Emergency_IRQ_o                ( s_emergency_IRQ_link              ),
      .Emergency_interrupt_clear_o    ( Emergency_clear_interrupt_link    ),
      .Emergency_interrupt_status_i   ( Emergency_IRQ_status_link         ),

      .barrier_num_threads_o          ( barrier_team_num_threads_link     ),
      .barrier_store_o                ( barrier_store_link                ),
      .barrier_get_o                  ( barrier_get_link                  ),
      .barrier_clear_req_o            ( clear_barrier_req_link            ),
      .Barrier_counter_i              ( barrier_counter_link              ),
      .mask_to_trigger_o              ( mask_to_trigger_link              ),
      .r_core_clk_gate_stat_o         ( core_status                       ),

      .r_clkgate_P                    ( r_clkgate_p_link                  ),
      `ifdef FEATURE_IDLE_CNT
      .clear_cnt_o                    ( s_clear_cnt_link                  ),
      .start_cnt_o                    ( s_start_cnt_link                  ),
      .idle_cyc_cnt_i                 ( r_cnt_link                        ),
      `endif
      .internal_event_o               ( s_internal_event_link             ),

      .speriph_slave                  ( speriph_slave                     ),
      .bbmux_bus                      ( bbmux_bus                         )
    );

    generate
      for ( i = 0; i < NUM_CORES; i++ )
      begin : event_unit_mux
        event_unit_mux
        #(
          .NUM_CORES(NUM_CORES)
        )
        event_unit_mux_i
        (
          .clk_i                      ( clk_i                            ),
          .rst_ni                     ( rst_ni                           ),
          .barrier_event_i            ( s_barrier_event_link[i]          ),
          .GP_events_i                ( s_GP_event[i]                    ),
          .tmr_events_i               ( cluster_events_i[3:0]            ),
          .dma_events_i               ( dma_events[i]                    ),
          .hwce_events_i              ( hwce_events                      ),
          .ext_events_i               ( r_ext_event_synched              ),
          .emergency_event_i          ( s_emergency_event_link[i]        ),
          .emergency_event_clear_i    ( Emergency_clear_evnt_link[i]     ),
          .emergency_event_status_o   ( Emergency_evnt_status_link[i]    ),
          .r_event_detect_o           ( r_event_detect_link[i]           ),
          .evnt_buffer_clear_i        ( evnt_buffer_clear_link[i]        ),
          .evnt_mask_sel_i            ( evnt_mask_sel_link[i]            ),
          .evnt_mask_i                ( s_evnt_mask_link[i]              ),
          .event_buffer_status_low_o  ( event_buffer_status_low_link[i]  ),
          .event_buffer_status_high_o ( event_buffer_status_high_link[i] ),
          .r_mask_o                   ( r_evnt_mask_reg_link[i]          )
        );
      end
    endgenerate

    generate
      for ( i = 0; i < NUM_CORES; i++ ) begin : interrupt_mask_gen
        interrupt_mask
        #(
            .NUM_CORES(NUM_CORES)
        )
        interrupt_mask_i
        (
          .clk_i                          ( clk_i                                ),
          .rst_ni                         ( rst_ni                               ),
          .interrupt_buffer_clear_i       ( interrupt_buffer_clear_link[i]       ),
          .barrier_interrupt_i            ( s_barrier_event_link[i]              ),
          .GP_interrupt_i                 ( s_GP_event[i]                        ),
          .tmr_interrupt_i                ( cluster_events_i[3:0]                ),
          .dma_interrupt_i                ( dma_events[i]                        ),
          .hwce_interrupt_i               ( hwce_events                          ),
          .ext_interrupt_i                ( r_ext_event_synched                  ),
          .emergency_interrupt_i          ( s_emergency_IRQ_link[i]              ),
          .emergency_interrupt_clear_i    ( Emergency_clear_interrupt_link[i]    ),
          .emergency_interrupt_status_o   ( Emergency_IRQ_status_link[i]         ),
          .interrupt_mask_sel_i           ( interrupt_mask_sel_link[i]           ),
          .interrupt_mask_i               ( s_interrupt_mask_link[i]             ),
          .IRQ_o                          ( IRQ_link[i]                          ),
          .NMIRQ_o                        ( NMIRQ_link[i]                        ),
          .interrupt_buffer_status_low_o  ( interrupt_buffer_status_low_link[i]  ),
          .interrupt_buffer_status_high_o ( interrupt_buffer_status_high_link[i] ),
          .r_mask_o                       ( r_interrupt_mask_reg_link[i]         )
        );
      end
    endgenerate


    generate
      for ( i = 0; i < NUM_CORES; i++ ) begin : event_unit_sm
        event_unit_sm
        #(
            .NUM_CORES(NUM_CORES)
        )
        event_unit_SM_i
        (
          .clk_i                  ( clk_i                  ),
          .rst_ni                 ( rst_ni                 ),
          .IRQ_i                  ( s_IRQ_or_NMIRQ[i]      ),
          .s_clk_stop_i           ( s_clk_stop_link[i]     ),
          .ready_to_shutdown_i    ( ready_to_shutdown_i[i] ),
          .r_event_detect_i       ( r_event_detect_link[i] ),
          .fetch_en_o             ( s_fetch_en_link[i]     ),
          `ifdef FEATURE_IDLE_CNT
          .clear_cnt_i            ( s_clear_cnt_link[i]    ),
          .start_cnt_i            ( s_start_cnt_link[i]    ),
          .idle_cyc_cnt_o         ( r_cnt_link[i]          ),
          `endif
          .clk_gate_core_o        ( clk_gate_core_link[i]  )
        );
      end
    endgenerate

    HW_barrier
    #(
        .NUM_CORES(NUM_CORES)
    )
    HW_barrier_i
    (
        .clk_i               ( clk_i                         ),
        .rst_ni              ( rst_ni                        ),
        .team_num_threads_i  ( barrier_team_num_threads_link ),
        .store_team_data_i   ( barrier_store_link            ),
        .barrier_get_i       ( barrier_get_link              ),
        .mask_to_trigger_i   ( mask_to_trigger_link          ),
        .clear_barrier_req_i ( clear_barrier_req_link        ),
        .barrier_event_o     ( barrier_event_link            ),
        .barrier_counter_o   ( barrier_counter_link          )
    );



    assign fetch_en_o = s_fetch_en_link;
    assign IRQ_o = IRQ_link;
    assign NMIRQ_o = NMIRQ_link;
    assign s_barrier_event_link = s_internal_event_link[0] ^ barrier_event_link;

    always_comb
    begin
      for(int i = 0; i<NUM_CORES; i++)
      begin
        for(int j = 0; j < `GP_EVNT; j++)
        begin
          s_GP_event[i][j] = s_internal_event_link[j+1][i];
        end
      end
    end


    assign clkgate_bus.clkgate_tcdm  =  r_clkgate_p_link[3:0];
    assign clkgate_bus.clkgate_int   =  r_clkgate_p_link[4];
    assign clkgate_bus.clkgate_scm   =  r_clkgate_p_link[5];
    assign clkgate_bus.clkgate_hwacc =  r_clkgate_p_link[6];

    generate
        for(  i = 0 ; i < NUM_CORES; i++ )
        begin : CLKGATE_CORE_BIND
              assign clkgate_bus.clkgate_core[i] = clk_gate_core_link[i];
        end
    endgenerate
endmodule
