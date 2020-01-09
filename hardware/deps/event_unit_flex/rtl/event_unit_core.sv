// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module event_unit_core
#(
  parameter NB_CORES = 4,
  parameter NB_SW_EVT = 8,
  parameter NB_BARR = NB_CORES/2,
  parameter NB_HW_MUT = 2,
  parameter MUTEX_MSG_W = 32,
  parameter PER_ID_WIDTH  = 5
)
(
  // clock and reset
  input  logic clk_i,
  input  logic rst_ni,
  input  logic test_mode_i,

  // master event lines, partially private for a specific core
  input  logic [31:0] master_event_lines_i,

  // sw event generation output
  output logic [NB_SW_EVT-1:0] core_sw_events_o,
  output logic [NB_CORES-1:0]  core_sw_events_mask_o,

  // barrier trigger output
  output logic [NB_BARR-1:0]   hw_barr_id_o,

  // request and message for mutex units
  output logic [NB_HW_MUT-1:0]                  mutex_rd_req_o,
  output logic [NB_HW_MUT-1:0]                  mutex_wr_req_o,
  output logic [NB_HW_MUT-1:0][MUTEX_MSG_W-1:0] mutex_msg_wdata_o,
  input  logic [NB_HW_MUT-1:0][MUTEX_MSG_W-1:0] mutex_msg_rdata_i,

  // signals for entry point dispatch
  output logic        dispatch_pop_req_o,
  output logic        dispatch_pop_ack_o,
  input  logic [31:0] dispatch_value_i,

  output logic        dispatch_w_req_o,
  output logic [31:0] dispatch_w_data_o,
  output logic [1:0]  dispatch_reg_sel_o,

  // clock and interrupt request to core
  output logic        core_irq_req_o,
  output logic [4:0]  core_irq_id_o,
  input  logic        core_irq_ack_i,
  input  logic [4:0]  core_irq_ack_id_i,

  input  logic        core_busy_i,
  output logic        core_clock_en_o,

  input  logic        dbg_req_i,
  output logic        core_dbg_req_o,

  // periph bus slave for regular register access
  XBAR_PERIPH_BUS.Slave periph_int_bus_slave,
  // demuxed periph for fast register access and event trigger
  XBAR_PERIPH_BUS.Slave eu_direct_link_slave

);

  // registers
  logic [31:0] event_mask_DP;
  logic [31:0] irq_mask_DP;
  logic [31:0] event_buffer_DP, event_buffer_DN;

  logic        irq_req_del_SP, irq_req_del_SN;
  logic        dbg_req_del_SP, dbg_req_del_SN;

  logic [NB_CORES-1:0] sw_events_mask_DP;
  logic                wait_clear_access_SP, wait_clear_access_SN;
  logic                wakeup_event, wakeup_mask_irq_SP;

  logic                trigger_release_SP, trigger_release_SN;

  // calculated write data
  logic [31:0] wdata_event_mask_demux, wdata_event_mask_interc;
  logic [31:0] wdata_irq_mask_demux, wdata_irq_mask_interc;
  logic [31:0] wdata_event_buffer_demux, wdata_event_buffer_interc;

  logic [NB_CORES-1:0] wdata_sw_events_mask_demux, wdata_sw_events_mask_interc;

  // write control
  logic [3:0]  we_demux, we_interc;

  // combinational signals
  logic [31:0] event_buffer_masked, irq_buffer_masked;
  logic        write_conflict, demux_add_is_sleep, demux_add_is_clear;
  logic        stop_core_clock, core_clock_en;

  logic [31:0] irq_clear_mask;
  logic [4:0]  irq_sel_id;
  logic        irq_pending;

  // multiple sources for sw events (write to trigger and read from wait regs)
  logic [NB_SW_EVT-1:0] sw_events_reg, sw_events_wait;
  logic [NB_CORES-1:0]  sw_events_mask_reg, sw_events_mask_wait;

  // (delayed) bus signals
  logic        p_interc_vld_SP, p_interc_vld_SN;
  logic        p_interc_gnt;
  logic        p_interc_req_del_SP, p_interc_req_del_SN;
  logic        p_interc_wen_del_SP, p_interc_wen_del_SN;
  logic [3:0]  p_interc_add_del_SP, p_interc_add_del_SN;

  logic        p_demux_vld_SP, p_demux_vld_SN;
  logic        p_demux_gnt, p_demux_gnt_sleep_fsm;
  logic        p_demux_req_del_SP, p_demux_req_del_SN;
  logic        p_demux_wen_del_SP, p_demux_wen_del_SN;
  logic [7:0]  p_demux_add_del_SP, p_demux_add_del_SN;

  // core clock FSM
  enum logic [1:0] { ACTIVE=0, SLEEP=1, IRQ_WHILE_SLEEP=2 } core_clock_CS, core_clock_NS;

  // ORing of sw event sources
  assign core_sw_events_o      = sw_events_reg | sw_events_wait;
  assign core_sw_events_mask_o = sw_events_mask_reg | sw_events_mask_wait;

  // masking and reduction of buffer
  assign event_buffer_masked   = event_buffer_DP & event_mask_DP;
  assign irq_buffer_masked     = event_buffer_DP & irq_mask_DP;

  // calculation of one-hot clear mask for interrupts
  assign irq_pending           = |irq_buffer_masked;
  assign irq_clear_mask        = (core_irq_ack_i) ? ~(1'b1 << core_irq_ack_id_i) : '1;

  // req/ack handling scheme for interrupts
  assign irq_req_del_SN        = irq_pending;
  assign core_irq_req_o        = irq_req_del_SP;
  assign core_irq_id_o         = irq_sel_id;

  // delaying of debug request to align to interrupt FSM handling
  assign dbg_req_del_SN        = dbg_req_i;
  assign core_dbg_req_o        = dbg_req_del_SP;

  // handshake for dispatch value consumption
  assign dispatch_pop_ack_o    = wakeup_event;

  // handle sleeping requests and conflicting write accesses
  assign demux_add_is_sleep    = ( ({eu_direct_link_slave.add[9:8],eu_direct_link_slave.add[5:3]} == 5'b00_111)      || // core regs _wait and _wait_clear
                                   ( eu_direct_link_slave.add[9:6] == 4'b0_101)                                      || // sw events _wait
                                   ( eu_direct_link_slave.add[9:6] == 4'b0_110)                                      || // sw events _wait_clear
                                   ({eu_direct_link_slave.add[9],eu_direct_link_slave.add[4:2]} == 4'b1_110)         || // barriers _wait
                                   ({eu_direct_link_slave.add[9],eu_direct_link_slave.add[4:2]} == 4'b1_111)         || // barriers _wait_clear
                                   ( eu_direct_link_slave.add[9:6] == 4'b0_011)                                      || // hw mutexes
                                   ({eu_direct_link_slave.add[9:6],eu_direct_link_slave.add[3:2]} == 6'b0010_00 ) );    // hw dispatch fifo_read

  assign demux_add_is_clear    = ( ( eu_direct_link_slave.add[9:2] == 8'b00_0011_11)                                 || // core regs _wait_clear
                                   ( eu_direct_link_slave.add[9:6] == 4'b01_10)                                      || // sw events _wait_clear
                                   ({eu_direct_link_slave.add[9],eu_direct_link_slave.add[4:2]} == 4'b1_111)         || // barriers _wait_clear
                                   ( eu_direct_link_slave.add[9:6] == 4'b00_11)                                      || // hw mutex units - always _wait_clear
                                   ({eu_direct_link_slave.add[9:6],eu_direct_link_slave.add[3:2]} == 6'b0010_00 ) );    // hw dispatch fifo_read
   
  assign stop_core_clock       = ( (eu_direct_link_slave.req == 1'b1) && (eu_direct_link_slave.wen == 1'b1) && (demux_add_is_sleep == 1'b1) );
  
  assign write_conflict        = ( ({periph_int_bus_slave.req, eu_direct_link_slave.req} == 2'b11) &&
                                   ({periph_int_bus_slave.wen, eu_direct_link_slave.wen} == 2'b00)    );

  // link from peripheral demux
  assign p_demux_gnt      = eu_direct_link_slave.req & p_demux_gnt_sleep_fsm & ~wait_clear_access_SP;
  assign p_demux_vld_SN   = p_demux_gnt;

  assign eu_direct_link_slave.gnt     = p_demux_gnt;
  assign eu_direct_link_slave.r_id    = '0;
  assign eu_direct_link_slave.r_opc   = 1'b0;
  assign eu_direct_link_slave.r_valid = p_demux_vld_SP;

  assign p_demux_req_del_SN  = eu_direct_link_slave.req;
  assign p_demux_wen_del_SN  = eu_direct_link_slave.wen;
  assign p_demux_add_del_SN  = eu_direct_link_slave.add[9:2];


  // link from peripheral interconnect
  assign p_interc_gnt     = ( (periph_int_bus_slave.req == 1'b1) && (write_conflict == 1'b0) );
  assign p_interc_vld_SN  = p_interc_gnt;

  assign periph_int_bus_slave.gnt     = p_interc_gnt;
  assign periph_int_bus_slave.r_opc   = 1'b0;
  assign periph_int_bus_slave.r_valid = p_interc_vld_SP;
  assign periph_int_bus_slave.r_id    = '0;

  assign p_interc_req_del_SN = periph_int_bus_slave.req;
  assign p_interc_wen_del_SN = periph_int_bus_slave.wen;
  assign p_interc_add_del_SN = periph_int_bus_slave.add[5:2];


  //write logic for demux and interconnect port
  always_comb begin
    // keep old buffer state and buffer newly triggered events
    event_buffer_DN   = (event_buffer_DP | master_event_lines_i) & irq_clear_mask;

    // default: don't write any register
    we_demux                    = '0;
    wdata_event_mask_demux      = '0;
    wdata_irq_mask_demux        = '0;
    wdata_event_buffer_demux    = '0;
    wdata_sw_events_mask_demux  = '0;

    we_interc                   = '0;
    wdata_event_mask_interc     = '0;
    wdata_irq_mask_interc       = '0;
    wdata_event_buffer_interc   = '0;
    wdata_sw_events_mask_interc = '0;

    // default: don't trigger any sw event or barrier
    sw_events_reg      = '0;
    sw_events_mask_reg = '0;

    // default: don't unlock (write) a mutex
    mutex_wr_req_o     = '0;
    mutex_msg_wdata_o  = '0;

    // default: don't push a value to or configure the HW dispatch
    dispatch_w_req_o   = 1'b0;
    dispatch_w_data_o  = '0;
    dispatch_reg_sel_o = '0; 

    // periph demux write access
    if ( (eu_direct_link_slave.req == 1'b1) && (eu_direct_link_slave.wen == 1'b0) ) begin
      casex (eu_direct_link_slave.add[9:6]) // decode reg group
        4'b00_00: begin
          // eu core registers
          case (eu_direct_link_slave.add[5:2])
            4'h0: begin we_demux[0] = 1'b1; wdata_event_mask_demux       = eu_direct_link_slave.wdata;                                    end
            4'h1: begin we_demux[0] = 1'b1; wdata_event_mask_demux       = event_mask_DP & ~eu_direct_link_slave.wdata;                   end
            4'h2: begin we_demux[0] = 1'b1; wdata_event_mask_demux       = event_mask_DP | eu_direct_link_slave.wdata;                    end
            4'h3: begin we_demux[1] = 1'b1; wdata_irq_mask_demux         = eu_direct_link_slave.wdata;                                    end
            4'h4: begin we_demux[1] = 1'b1; wdata_irq_mask_demux         = irq_mask_DP & ~eu_direct_link_slave.wdata;                     end
            4'h5: begin we_demux[1] = 1'b1; wdata_irq_mask_demux         = irq_mask_DP | eu_direct_link_slave.wdata;                      end
            4'ha: begin we_demux[2] = 1'b1; wdata_event_buffer_demux     = event_buffer_DP & ~eu_direct_link_slave.wdata;                 end
            4'hb: begin we_demux[3] = 1'b1; wdata_sw_events_mask_demux   = eu_direct_link_slave.wdata[NB_CORES-1:0];                      end
            4'hc: begin we_demux[3] = 1'b1; wdata_sw_events_mask_demux   = sw_events_mask_DP & ~eu_direct_link_slave.wdata[NB_CORES-1:0]; end
            4'hd: begin we_demux[3] = 1'b1; wdata_sw_events_mask_demux   = sw_events_mask_DP | eu_direct_link_slave.wdata[NB_CORES-1:0];  end
          endcase
        end
        4'b00_10: begin
          // hw dispatch
          dispatch_w_req_o   = 1'b1;
          dispatch_w_data_o  = eu_direct_link_slave.wdata;
          dispatch_reg_sel_o = eu_direct_link_slave.add[3:2];
        end
        4'b00_11: begin
          // hw mutexes
          mutex_wr_req_o[eu_direct_link_slave.add[5:2]]    = 1'b1;
          mutex_msg_wdata_o[eu_direct_link_slave.add[5:2]] = eu_direct_link_slave.wdata;
        end
        4'b01_??: begin
          // handle sw event triggering
          if ( eu_direct_link_slave.add[7:6] == 2'b00 )  begin
            sw_events_reg[eu_direct_link_slave.add[4:2]] = 1'b1;
            // use all-0 state to trigger all cores
            if ( eu_direct_link_slave.wdata[NB_CORES-1:0] == '0 )
              sw_events_mask_reg = '1;
            else
              sw_events_mask_reg = eu_direct_link_slave.wdata[NB_CORES-1:0];
          end
        end
      endcase
    end

    // periph interconnect write access
    if ( (periph_int_bus_slave.req == 1'b1) && (periph_int_bus_slave.wen == 1'b0) ) begin
      case (periph_int_bus_slave.add[5:2])
        4'h0: begin we_interc[0] = 1'b1; wdata_event_mask_interc     = periph_int_bus_slave.wdata;                                    end
        4'h1: begin we_interc[0] = 1'b1; wdata_event_mask_interc     = event_mask_DP & ~periph_int_bus_slave.wdata;                   end
        4'h2: begin we_interc[0] = 1'b1; wdata_event_mask_interc     = event_mask_DP | periph_int_bus_slave.wdata;                    end
        4'h3: begin we_interc[1] = 1'b1; wdata_irq_mask_interc       = periph_int_bus_slave.wdata;                                    end
        4'h4: begin we_interc[1] = 1'b1; wdata_irq_mask_interc       = irq_mask_DP & ~periph_int_bus_slave.wdata;                     end
        4'h5: begin we_interc[1] = 1'b1; wdata_irq_mask_interc       = irq_mask_DP | periph_int_bus_slave.wdata;                      end
        4'ha: begin we_interc[2] = 1'b1; wdata_event_buffer_interc   = event_buffer_DP & ~periph_int_bus_slave.wdata;                 end
        4'hb: begin we_interc[3] = 1'b1; wdata_sw_events_mask_interc = periph_int_bus_slave.wdata[NB_CORES-1:0];                      end
        4'hc: begin we_interc[3] = 1'b1; wdata_sw_events_mask_interc = sw_events_mask_DP & ~periph_int_bus_slave.wdata[NB_CORES-1:0]; end
        4'hd: begin we_interc[3] = 1'b1; wdata_sw_events_mask_interc = sw_events_mask_DP | periph_int_bus_slave.wdata[NB_CORES-1:0];  end
      endcase
    end

    if ( wait_clear_access_SP == 1'b1 )
      event_buffer_DN = ((event_buffer_DP | master_event_lines_i) & ~event_mask_DP) & irq_clear_mask;
    else if ( we_demux[2] == 1'b1 )
      event_buffer_DN = (wdata_event_buffer_demux | master_event_lines_i) & irq_clear_mask;
    else if ( we_interc[2] == 1'b1 )
      event_buffer_DN = (wdata_event_buffer_interc | master_event_lines_i) & irq_clear_mask;

  end

  // read muxes for both links
  always_comb begin
    eu_direct_link_slave.r_rdata = '0;
    periph_int_bus_slave.r_rdata = '0;

    // default: don't trigger any sw event or barrier or mutex
    sw_events_wait      = '0;
    sw_events_mask_wait = '0;
    hw_barr_id_o        = '0;
    mutex_rd_req_o      = '0;

    // default: dont'r request to pop a value from the dispatch FIFO
    dispatch_pop_req_o  = 1'b0;

    // read accesses for periph demux port; inclues _wait and _wait_clear regs
    if ( (p_demux_req_del_SP == 1'b1) && (p_demux_wen_del_SP == 1'b1) ) begin
      case (p_demux_add_del_SP[7:4]) // decode reg group
        4'b00_00: begin // eu core registers
          case (p_demux_add_del_SP[3:0])
            4'h0: eu_direct_link_slave.r_rdata = event_mask_DP;
            4'h3: eu_direct_link_slave.r_rdata = irq_mask_DP;
            4'h6: eu_direct_link_slave.r_rdata = {31'b0, core_clock_en};
            4'h7: eu_direct_link_slave.r_rdata = event_buffer_DP;
            4'h8: eu_direct_link_slave.r_rdata = event_buffer_masked;
            4'h9: eu_direct_link_slave.r_rdata = irq_buffer_masked;
            4'hb: eu_direct_link_slave.r_rdata = {{(32-NB_CORES){1'b0}}, sw_events_mask_DP};
            4'he: eu_direct_link_slave.r_rdata = event_buffer_masked;
            4'hf: eu_direct_link_slave.r_rdata = event_buffer_masked;
          endcase
        end
        4'b00_10: begin // hw dispatch pop request
          if ( p_demux_add_del_SP[1:0] == 2'b00 )
            eu_direct_link_slave.r_rdata = dispatch_value_i;
        end
        // mutex read/lock request
        4'b00_11: eu_direct_link_slave.r_rdata = mutex_msg_rdata_i[p_demux_add_del_SP[3:0]];
        // some wait register for either sw_event or barrier
        default:  eu_direct_link_slave.r_rdata = event_buffer_masked;
        //4'b0101,4'b0110,4'b1011,4'b1100: eu_direct_link_slave.r_rdata = event_buffer_masked;
      endcase
    end

    if ( eu_direct_link_slave.req & eu_direct_link_slave.wen & trigger_release_SP ) begin
      // trigger sw_event+read buffer+sleep(+clear) accesses
      if ( (eu_direct_link_slave.add[9:6] == 4'b0101) || (eu_direct_link_slave.add[9:6] == 4'b0110) ) begin
        sw_events_wait[eu_direct_link_slave.add[4:2]] = 1'b1;
        // use all-0 state to trigger all cores
        if ( sw_events_mask_DP == '0 )
          sw_events_mask_wait = '1;
        else
          sw_events_mask_wait = sw_events_mask_DP;
      end

      // trigger hw_barrier+read buffer(+sleep)(+clear) accesses
      if ( ({eu_direct_link_slave.add[9],eu_direct_link_slave.add[4:2]} == 4'b1_101) ||
           ({eu_direct_link_slave.add[9],eu_direct_link_slave.add[4:2]} == 4'b1_110) ||
           ({eu_direct_link_slave.add[9],eu_direct_link_slave.add[4:2]} == 4'b1_111)    )
      begin
        hw_barr_id_o[eu_direct_link_slave.add[8:5]] = 1'b1;
      end

      // try to lock a mutex
      if ( eu_direct_link_slave.add[9:6] == 4'b0_011 )
        mutex_rd_req_o[eu_direct_link_slave.add[5:2]] = 1'b1;

      // try to pop a value from the dispatch FIFO
      if ( eu_direct_link_slave.add[9:2] == 8'b0_01000_00 )
        dispatch_pop_req_o = 1'b1;

    end

    // only regular read accesses for interconnect port
    if ( (p_interc_req_del_SP == 1'b1) && (p_interc_wen_del_SP == 1'b1) ) begin
      case (p_interc_add_del_SP)
        4'h0: periph_int_bus_slave.r_rdata = event_mask_DP;
        4'h3: periph_int_bus_slave.r_rdata = irq_mask_DP;
        4'h6: periph_int_bus_slave.r_rdata = {31'b0, core_clock_en};
        4'h7: periph_int_bus_slave.r_rdata = event_buffer_DP;
        4'h8: periph_int_bus_slave.r_rdata = event_buffer_masked;
        4'h9: periph_int_bus_slave.r_rdata = irq_buffer_masked;
        4'hb: periph_int_bus_slave.r_rdata = {{(32-NB_CORES){1'b0}}, sw_events_mask_DP};
      endcase
    end
  end


  // FSM for controlling the core clock
  always_comb begin
    core_clock_NS         = core_clock_CS;
    core_clock_en         = 1'b1;
    p_demux_gnt_sleep_fsm = 1'b1;
    wait_clear_access_SN  = 1'b0;
    wakeup_event          = 1'b0;

    trigger_release_SN    = trigger_release_SP;

    case (core_clock_CS)
      ACTIVE: begin
        // check if there is any sleep request at all
        if ( stop_core_clock ) begin
          // If there is already an irq request sent to the core, the replay is not properly detected.
          if ( irq_pending | dbg_req_i ) begin
            // avoids split/illegal transactions (gnt but no r_valid) 
            p_demux_gnt_sleep_fsm = 1'b0;
            trigger_release_SN    = 1'b0;
            core_clock_NS = IRQ_WHILE_SLEEP;
          end
          else begin
            // corner-case: event already triggered while going to sleep
            if ( |event_buffer_masked ) begin
              // make sure the next req can trigger units again
              trigger_release_SN = 1'b1;
              // signal state change through incoming event
              wakeup_event = 1'b1;
              // handle buffer clear cases
              if ( demux_add_is_clear )
                wait_clear_access_SN = 1'b1;
            end
            else begin
              p_demux_gnt_sleep_fsm = 1'b0;
              // block further unit triggering until return to ACTIVE
              trigger_release_SN = 1'b0;
              if ( ~core_busy_i ) core_clock_NS = SLEEP;
            end
          end
        end
      end
      SLEEP: begin
        core_clock_en         = 1'b0;
        p_demux_gnt_sleep_fsm = 1'b0;

        if ( irq_pending | dbg_req_i ) begin
          core_clock_en = 1'b1;
          core_clock_NS = IRQ_WHILE_SLEEP;
        end
        else if ( |event_buffer_masked ) begin
          core_clock_en = 1'b1;

          if ( demux_add_is_clear ) wait_clear_access_SN = 1'b1;
          p_demux_gnt_sleep_fsm = 1'b1;
          wakeup_event          = 1'b1;

          trigger_release_SN = 1'b1;
          core_clock_NS = ACTIVE;
        end
      end
      IRQ_WHILE_SLEEP: begin
        if ( stop_core_clock ) begin
          if ( ~irq_pending & ~dbg_req_i ) begin   
            if ( |event_buffer_masked ) begin
              core_clock_en = 1'b1;

              if ( demux_add_is_clear ) wait_clear_access_SN = 1'b1;
              p_demux_gnt_sleep_fsm = 1'b1;
              wakeup_event          = 1'b1;

              trigger_release_SN = 1'b1;
              core_clock_NS = ACTIVE;
            end
            else begin
              p_demux_gnt_sleep_fsm = 1'b0;
              if ( ~core_busy_i ) core_clock_NS = SLEEP;
            end
          end
        end
      end
    endcase
  end

  assign core_clock_en_o = core_clock_en;

  // find first leading 1 for current irq priorization scheme
  fl1_loop #(
    .WIDTH(32) )
  fl1_loop_i (
    .vector_i(irq_buffer_masked),
    .idx_bin_o(irq_sel_id),
    .no1_o()
  );

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if ( rst_ni == 1'b0 ) begin
      core_clock_CS        <= ACTIVE;
      event_mask_DP        <= '0;
      irq_mask_DP          <= '0;
      irq_req_del_SP       <= '0;
      dbg_req_del_SP       <= '0;
      event_buffer_DP      <= '0;
      wait_clear_access_SP <= 1'b0;
      trigger_release_SP   <= 1'b1;
      sw_events_mask_DP    <= '0;

      p_demux_vld_SP       <= 1'b0;
      p_demux_add_del_SP   <= '0;
      p_demux_req_del_SP   <= 1'b0;
      p_demux_wen_del_SP   <= 1'b0;
      p_interc_vld_SP      <= 1'b0;
      p_interc_add_del_SP  <= '0;
      p_interc_req_del_SP  <= 1'b0;
      p_interc_wen_del_SP  <= 1'b0;


      wakeup_mask_irq_SP   <= '0;
    end
    else begin
      core_clock_CS        <= core_clock_NS;

      // write arbiters - demux write access takes priority
      if ( we_demux[0] == 1'b1 )
        event_mask_DP   <= wdata_event_mask_demux;
      else if ( we_interc[0] == 1'b1 )
        event_mask_DP   <= wdata_event_mask_interc;

      if ( we_demux[1] == 1'b1 )
        irq_mask_DP     <= wdata_irq_mask_demux;
      else if ( we_interc[1] == 1'b1 )
        irq_mask_DP     <= wdata_irq_mask_interc;

      if ( wait_clear_access_SP | core_irq_ack_i | (|master_event_lines_i) | we_demux[2] | we_interc[2] )
        event_buffer_DP <= event_buffer_DN;

      if ( we_demux[3] == 1'b1 )
        sw_events_mask_DP <= wdata_sw_events_mask_demux;
      else if ( we_interc[3] == 1'b1 )
        sw_events_mask_DP <= wdata_sw_events_mask_interc;

      irq_req_del_SP       <= irq_req_del_SN;

      dbg_req_del_SP       <= dbg_req_del_SN;

      wait_clear_access_SP <= wait_clear_access_SN;

      wakeup_mask_irq_SP   <= wakeup_event;

      trigger_release_SP   <= trigger_release_SN;

      p_demux_req_del_SP   <= p_demux_req_del_SN;
      p_demux_wen_del_SP   <= p_demux_wen_del_SN;
      p_demux_vld_SP       <= p_demux_vld_SN;

      if(eu_direct_link_slave.req & eu_direct_link_slave.gnt)
        p_demux_add_del_SP   <= p_demux_add_del_SN;

      p_interc_req_del_SP  <= p_interc_req_del_SN;
      p_interc_wen_del_SP  <= p_interc_wen_del_SN;
      p_interc_vld_SP      <= p_interc_vld_SN;

      if(periph_int_bus_slave.req & periph_int_bus_slave.gnt)
        p_interc_add_del_SP  <= p_interc_add_del_SN;

    end
  end

  // covergroup instantiation
`ifdef COVERGROUP_ANALYSIS
  // synopsys translate_off
	event_unit_core_monitor event_unit_core_monitor_i (
		.clk_i              ( clk_i           ),
	
		.FSM_state_i        ( core_clock_CS        ),
		.event_pending_i    ( |event_buffer_masked ),
		.irq_pending_i      ( irq_pending          ),
		.irq_req_i          ( irq_req_del_SP       ),
		.wakeup_event_i     ( wakeup_event         ),
		.wakeup_mask_irq_i  ( wakeup_mask_irq_SP   )
	);
  // synopsys translate_on
`endif

endmodule // event_unit_core

module fl1_loop
#(
  parameter WIDTH = 4
)
(
  input  logic [WIDTH-1:0]         vector_i,
  output logic [$clog2(WIDTH)-1:0] idx_bin_o,
  output logic                     no1_o
);

  assign no1_o = ~(|vector_i);

  logic found;

  always_comb begin
    found     = 1'b0;
    idx_bin_o = '0;

    for (int i = WIDTH-1; i > 0; i--) begin
      if ( (vector_i[i] == 1'b1) && (found == 1'b0) ) begin
        found     = 1'b1;
        idx_bin_o = i;
      end
    end
  end

endmodule


// cover groups for corner-case verification
`ifdef COVERGROUP_ANALYSIS
// synopsys translate_off
module event_unit_core_monitor (
	input  logic        clk_i,
	
	input  logic  [1:0] FSM_state_i,
	input  logic        event_pending_i,
	input  logic        irq_pending_i,
	input  logic        irq_req_i,
	input  logic        wakeup_event_i,
	input  logic        wakeup_mask_irq_i
);

	typedef enum logic [1:0] { ACTIVE=0, SLEEP=1, IRQ_WHILE_SLEEP=2 } FSM_state_t;

	FSM_state_t FSM_state;

	logic event_pending_del, irq_pending_del;
	logic event_rise, irq_rise;

	assign FSM_state = FSM_state_t'(FSM_state_i);

	always_ff @(posedge clk_i) begin
		event_pending_del <= event_pending_i;
		irq_pending_del   <= irq_pending_i;
	end

	assign event_rise = ~event_pending_del & event_pending_i;
	assign irq_rise   = ~irq_pending_del & irq_pending_i;

	covergroup irq_simul @(clk_i);
		type_option.merge_instances = 1;
		
		FSM_state_cp: coverpoint FSM_state {
			bins ACTIVE          = {ACTIVE};
			bins SLEEP           = {SLEEP};
			bins IRQ_WHILE_SLEEP = {IRQ_WHILE_SLEEP};
		}

		irq_rise_event_simul_cr: cross FSM_state_cp, event_pending_i, irq_rise {
			bins ACTIVE          = binsof(FSM_state_cp) intersect {ACTIVE}          && binsof(event_pending_i) intersect {1'b1} && binsof(irq_rise) intersect {1'b1};
			bins SLEEP           = binsof(FSM_state_cp) intersect {SLEEP}           && binsof(event_pending_i) intersect {1'b1} && binsof(irq_rise) intersect {1'b1};
			bins IRQ_WHILE_SLEEP = binsof(FSM_state_cp) intersect {IRQ_WHILE_SLEEP} && binsof(event_pending_i) intersect {1'b1} && binsof(irq_rise) intersect {1'b1};
			ignore_bins NO_IRQ   = binsof(irq_rise)        intersect {1'b0};
			ignore_bins NO_EVT   = binsof(event_pending_i) intersect {1'b0};
		}

		irq_event_rise_simul_cr: cross FSM_state_cp, event_rise, irq_pending_i {
			bins ACTIVE          = binsof(FSM_state_cp) intersect {ACTIVE}          && binsof(event_rise) intersect {1'b1} && binsof(irq_pending_i) intersect {1'b1};
			bins SLEEP           = binsof(FSM_state_cp) intersect {SLEEP}           && binsof(event_rise) intersect {1'b1} && binsof(irq_pending_i) intersect {1'b1};
			bins IRQ_WHILE_SLEEP = binsof(FSM_state_cp) intersect {IRQ_WHILE_SLEEP} && binsof(event_rise) intersect {1'b1} && binsof(irq_pending_i) intersect {1'b1};
			ignore_bins NO_IRQ   = binsof(irq_pending_i)  intersect {1'b0};
			ignore_bins NO_EVT   = binsof(event_rise)     intersect {1'b0};
		}

		irq_event_delayed_cr: cross FSM_state_cp, wakeup_mask_irq_i, irq_pending_i {
			bins ACTIVE          = binsof(FSM_state_cp) intersect {ACTIVE}          && binsof(wakeup_mask_irq_i) intersect {1'b1} && binsof(irq_pending_i) intersect {1'b1};
			bins SLEEP           = binsof(FSM_state_cp) intersect {SLEEP}           && binsof(wakeup_mask_irq_i) intersect {1'b1} && binsof(irq_pending_i) intersect {1'b1};
			bins IRQ_WHILE_SLEEP = binsof(FSM_state_cp) intersect {IRQ_WHILE_SLEEP} && binsof(wakeup_mask_irq_i) intersect {1'b1} && binsof(irq_pending_i) intersect {1'b1};
			ignore_bins NO_IRQ   = binsof(irq_pending_i)   intersect {1'b0};
			ignore_bins NO_EVT   = binsof(wakeup_mask_irq_i)  intersect {1'b0};
		}

		illegal_irq_req_event_delayed_cr: cross FSM_state_cp, wakeup_mask_irq_i, irq_req_i {
			bins ACTIVE          = binsof(FSM_state_cp) intersect {ACTIVE}          && binsof(wakeup_mask_irq_i) intersect {1'b1} && binsof(irq_req_i) intersect {1'b1};
			bins SLEEP           = binsof(FSM_state_cp) intersect {SLEEP}           && binsof(wakeup_mask_irq_i) intersect {1'b1} && binsof(irq_req_i) intersect {1'b1};
			bins IRQ_WHILE_SLEEP = binsof(FSM_state_cp) intersect {IRQ_WHILE_SLEEP} && binsof(wakeup_mask_irq_i) intersect {1'b1} && binsof(irq_req_i) intersect {1'b1};
			ignore_bins NO_IRQ   = binsof(irq_req_i)      intersect {1'b0};
			ignore_bins NO_EVT   = binsof(wakeup_mask_irq_i) intersect {1'b0};
		}

		irq_req_event_simul_cr: cross FSM_state_cp, event_pending_i, irq_req_i {
			bins ACTIVE          = binsof(FSM_state_cp) intersect {ACTIVE}          && binsof(event_pending_i) intersect {1'b1} && binsof(irq_req_i) intersect {1'b1};
			bins SLEEP           = binsof(FSM_state_cp) intersect {SLEEP}           && binsof(event_pending_i) intersect {1'b1} && binsof(irq_req_i) intersect {1'b1};
			bins IRQ_WHILE_SLEEP = binsof(FSM_state_cp) intersect {IRQ_WHILE_SLEEP} && binsof(event_pending_i) intersect {1'b1} && binsof(irq_req_i) intersect {1'b1};
			ignore_bins NO_IRQ   = binsof(irq_req_i)        intersect {1'b0};
			ignore_bins NO_EVT   = binsof(event_pending_i)  intersect {1'b0};
		}

		irq_req_wakeup_event_cr: cross FSM_state_cp, wakeup_event_i, irq_req_i {
			bins ACTIVE          = binsof(FSM_state_cp) intersect {ACTIVE}          && binsof(wakeup_event_i) intersect {1'b1} && binsof(irq_req_i) intersect {1'b1};
			bins SLEEP           = binsof(FSM_state_cp) intersect {SLEEP}           && binsof(wakeup_event_i) intersect {1'b1} && binsof(irq_req_i) intersect {1'b1};
			bins IRQ_WHILE_SLEEP = binsof(FSM_state_cp) intersect {IRQ_WHILE_SLEEP} && binsof(wakeup_event_i) intersect {1'b1} && binsof(irq_req_i) intersect {1'b1};
			ignore_bins NO_IRQ   = binsof(irq_req_i)      intersect {1'b0};
			ignore_bins NO_EVT   = binsof(wakeup_event_i) intersect {1'b0};
		}
	endgroup

	// don't forget covergroup instantiations
	irq_simul irq_simul_i = new;

endmodule
// synopsys translate_on
`endif
