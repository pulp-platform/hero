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
// Engineer:       Roberto Roncone - roncone@iis.ee.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                  Igor Loi - igor.loi@unibo.it                              //
//                                                                            //
// Create Date:    12/03/2015                                                 //
// Design Name:    event_unit                                                 //
// Module Name:    event_unit_input                                           //
// Project Name:   PULP                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:                                                               //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (19/03/2015) fixed concatenation  with unsized numbers     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "old_event_unit_defines.sv"

module event_unit_input
#(
    parameter NUM_CORES=4
)
(

    input logic                                            clk_i,
    input logic                                            rst_ni,

    ///EVENT SIGNALS
    input  logic [NUM_CORES-1:0]                           r_event_detect_i,
    output logic [NUM_CORES-1:0]                           s_clk_stop_o,
    input  logic [NUM_CORES-1:0][31:0]                     event_buffer_status_low_i,
    input  logic [NUM_CORES-1:0][31:0]                     event_buffer_status_high_i,
    output logic [NUM_CORES-1:0][63:0]                     evnt_buffer_clear_o,
    input  logic [NUM_CORES-1:0][63:0]                     evnt_mask_reg_i,
    output logic [NUM_CORES-1:0][63:0]                     evnt_mask_o,
    output logic [NUM_CORES-1:0][1:0]                      evnt_mask_sel_o,
    output logic [NUM_CORES-1:0]                           Emergency_event_o,
    output logic [NUM_CORES-1:0]                           Emergency_evnt_clear_o,
    input  logic [NUM_CORES-1:0]                           Emergency_event_status_i,
    ///INTERRUPT SIGNALS
    input  logic [NUM_CORES-1:0][31:0]                     interrupt_buffer_status_low_i,
    input  logic [NUM_CORES-1:0][31:0]                     interrupt_buffer_status_high_i,
    output logic [NUM_CORES-1:0][63:0]                     interrupt_buffer_clear_o,
    input  logic [NUM_CORES-1:0][63:0]                     interrupt_mask_reg_i,
    output logic [NUM_CORES-1:0][63:0]                     interrupt_mask_o,
    output logic [NUM_CORES-1:0][1:0]                      interrupt_mask_sel_o,
    output logic [NUM_CORES-1:0]                           Emergency_IRQ_o,
    output logic [NUM_CORES-1:0]                           Emergency_interrupt_clear_o,
    input  logic [NUM_CORES-1:0]                           Emergency_interrupt_status_i,
    //COMMON
    output logic [3:0][NUM_CORES-1:0]               internal_event_o,
    //HW BARRIER
    output logic [6-1:0][$clog2(NUM_CORES):0]  barrier_num_threads_o,
    output logic [6-1:0]                       barrier_store_o,
    output logic [6-1:0][NUM_CORES-1:0]        mask_to_trigger_o ,
    output logic [6-1:0]                       barrier_get_o,
    output logic [6-1:0]                       barrier_clear_req_o,
    input  logic [6-1:0][$clog2(NUM_CORES):0]  Barrier_counter_i,
    output logic [NUM_CORES-1:0]                           r_core_clk_gate_stat_o,
`ifdef FEATURE_IDLE_CNT
    output logic[NUM_CORES-1:0]                            clear_cnt_o,
    output logic[NUM_CORES-1:0]                            start_cnt_o,
    input  logic[NUM_CORES-1:0][31:0]                      idle_cyc_cnt_i,
`endif

    output logic [6:0]                                     r_clkgate_P,
    XBAR_PERIPH_BUS.Slave                                  speriph_slave,
    BBMUX_CONFIG_BUS.Master                                bbmux_bus
);

   localparam LOG_NUM_CORES = NUM_CORES <= 1 ? 1 : $clog2(NUM_CORES);

   //clkgate
   logic [6:0]                              ClkGate_P;
   logic [6:0]                              ClkGate_N;
   //bbmux
   logic [9:0][1:0]                         bbmux_P;
   logic [9:0][1:0]                         bbmux_N;

   logic                                    bbmux_sel_P;
   logic                                    bbmux_sel_N;

   logic [31:0]                             r_data;
   logic [31:0]                             r_data_p;
   logic [NUM_CORES:0]                      s_r_id; //NUM_CORES +1




   logic [NUM_CORES-1:0]                    s_clk_status;
   logic [NUM_CORES-1:0]                    r_clk_status;
   logic [NUM_CORES-1:0]                    s_Emergency_event;
   logic [NUM_CORES-1:0]                    s_Emergency_IRQ;
   logic [3:0][NUM_CORES-1:0]        s_internal_event;


   logic [NUM_CORES-1:0][31:0]              r_evnt_mask_low;
   logic [NUM_CORES-1:0][31:0]              r_evnt_mask_high;
   logic [NUM_CORES-1:0][31:0]              r_interrupt_mask_low;
   logic [NUM_CORES-1:0][31:0]              r_interrupt_mask_high;
   logic [NUM_CORES-1:0][31:0]              s_evnt_mask_low;
   logic [NUM_CORES-1:0][31:0]              s_evnt_mask_high;
   logic [NUM_CORES-1:0][31:0]              s_evnt_buffer_clear_low;
   logic [NUM_CORES-1:0][31:0]              s_evnt_buffer_clear_high;
   logic [NUM_CORES-1:0][31:0]              r_evnt_buffer_low;
   logic [NUM_CORES-1:0][31:0]              r_evnt_buffer_high;
   logic [NUM_CORES-1:0][31:0]              s_interrupt_mask_low;
   logic [NUM_CORES-1:0][31:0]              s_interrupt_mask_high;
   logic [NUM_CORES-1:0][31:0]              s_interrupt_buffer_clear_low;
   logic [NUM_CORES-1:0][31:0]              s_interrupt_buffer_clear_high;
   logic [NUM_CORES-1:0][31:0]              r_interrupt_buffer_low;
   logic [NUM_CORES-1:0][31:0]              r_interrupt_buffer_high;
   logic [NUM_CORES-1:0][63:0]              interrupt_buffer_status; //both low and high mask, used by the arbiter
   logic [NUM_CORES-1:0]                    interrupt_mask_sel_high;
   logic [NUM_CORES-1:0]                    interrupt_mask_sel_low;
   logic [NUM_CORES-1:0]                    evnt_mask_sel_high;
   logic [NUM_CORES-1:0]                    evnt_mask_sel_low;
   logic [NUM_CORES-1:0]                    s_emergency_evnt_clear;
   logic [NUM_CORES-1:0]                    s_emergency_interrupt_clear;
   logic [NUM_CORES-1:0][7:0]               IRQ_id;

   //HW BARRIER SIGNALS
   logic [6-1:0][$clog2(NUM_CORES):0] s_barrier_num_threads;
   logic [6-1:0]                      s_barrier_store;
   logic [6-1:0][NUM_CORES-1:0]       s_barrier_mask_to_trigg;
   logic [6-1:0]                      s_get_barrier;
   logic [6-1:0]                      s_clear_barrier_req;

   genvar                                         i;
   enum                                           logic { TRANS_IDLE, TRANS_REQ} CS, NS;


   assign internal_event_o            = s_internal_event;
   assign Emergency_event_o           = s_Emergency_event;
   assign Emergency_IRQ_o             = s_Emergency_IRQ;
   assign Emergency_evnt_clear_o      = s_emergency_evnt_clear;
   assign Emergency_interrupt_clear_o = s_emergency_interrupt_clear;
   assign r_core_clk_gate_stat_o      = r_clk_status;
   generate

      for( i=0; i< NUM_CORES; i++)
      begin : CORE_BINDING
           ///OUTPUT
           assign evnt_mask_o[i]              = { s_evnt_mask_high[i]             , s_evnt_mask_low[i]              };
           assign evnt_buffer_clear_o[i]      = { s_evnt_buffer_clear_high[i]     , s_evnt_buffer_clear_low[i]      };
           assign interrupt_mask_o[i]         = { s_interrupt_mask_high[i]        , s_interrupt_mask_low[i]         };
           assign interrupt_buffer_clear_o[i] = { s_interrupt_buffer_clear_high[i], s_interrupt_buffer_clear_low [i]};
           ///INPUT
           assign r_evnt_mask_low[i]    = evnt_mask_reg_i[i][31:0];
           assign r_evnt_mask_high[i]   = evnt_mask_reg_i[i][63:32];
           assign r_evnt_buffer_low[i]  = event_buffer_status_low_i[i];
           assign r_evnt_buffer_high[i] = event_buffer_status_high_i[i];
           assign evnt_mask_sel_o[i]    = { evnt_mask_sel_high[i] , evnt_mask_sel_low[i] };

           assign r_interrupt_mask_low[i]    = interrupt_mask_reg_i[i][31:0];
           assign r_interrupt_mask_high[i]   = interrupt_mask_reg_i[i][63:32];
           assign r_interrupt_buffer_low[i]  = interrupt_buffer_status_low_i[i];
           assign r_interrupt_buffer_high[i] = interrupt_buffer_status_high_i[i];
           assign interrupt_buffer_status[i] = { r_interrupt_buffer_high[i] ,r_interrupt_buffer_low[i]  };
           assign interrupt_mask_sel_o[i]    = { interrupt_mask_sel_high[i] , interrupt_mask_sel_low[i] };
      end
   endgenerate

   ///////////////////////////////////////////
   ////   HW BARRIER
   //////////////////////////////////////////

   generate
      for( i=0; i< 6; i++)
      begin : BARRIER_BINDING
            assign barrier_num_threads_o[i] = s_barrier_num_threads[i];
            assign barrier_store_o[i]       = s_barrier_store[i];
            assign mask_to_trigger_o[i]     = s_barrier_mask_to_trigg[i];
      end
   endgenerate

   assign barrier_get_o       = s_get_barrier;
   assign barrier_clear_req_o = s_clear_barrier_req;




   //////////////////////////////////
   //  INPUT LOGIC
   /////////////////////////////////
   assign speriph_slave.gnt = speriph_slave.req;

   always_comb
     begin : UPDATE_STATUS_REGISTERS

      speriph_slave.r_rdata = 32'b0;
      speriph_slave.r_valid = 1'b0;
      speriph_slave.r_id    = '0;

      ClkGate_N            = ClkGate_P;
      bbmux_N              = bbmux_P;
      bbmux_sel_N          = bbmux_sel_P;

      for( int i=0; i< NUM_CORES; i++)
        begin
         s_evnt_buffer_clear_high[i]      = 32'b0;
         s_evnt_buffer_clear_low[i]       = 32'b0;
         s_interrupt_buffer_clear_high[i] = 32'b0;
         s_interrupt_buffer_clear_low[i]  = 32'b0;
         s_emergency_interrupt_clear[i]   = 0;
         s_emergency_evnt_clear[i]        = 0;
         s_evnt_mask_high[i]              = 32'b0;
         s_evnt_mask_low[i]               = 32'b0;
         s_interrupt_mask_high[i]         = 32'b0;
         s_interrupt_mask_low[i]          = 32'b0;
         evnt_mask_sel_low[i]             = 0;
         evnt_mask_sel_high[i]            = 0;
         interrupt_mask_sel_low[i]        = 0;
         interrupt_mask_sel_high[i]       = 0;

        end

      s_Emergency_event =  {(NUM_CORES){1'b0}};
      s_Emergency_IRQ =  {(NUM_CORES){1'b0}};

      r_data = '0;

      NS = CS;

      s_clk_stop_o = '0;
      s_clk_status = r_clk_status;
      s_internal_event = {(3*NUM_CORES){1'b0}};

      s_barrier_num_threads   = '0;
      s_barrier_store         = '0;
      s_barrier_mask_to_trigg = '0;
      s_get_barrier           = '0;
`ifdef FEATURE_IDLE_CNT
      clear_cnt_o             = '0;
      start_cnt_o             = '0;
`endif
      s_clear_barrier_req     = '0;

      case(CS)

      TRANS_IDLE:
        begin
         if ( speriph_slave.req == 1'b1 )
           begin
            NS = TRANS_REQ;
            case({speriph_slave.add[9],speriph_slave.add[8],speriph_slave.wen})
            3'b000:
              begin
                 if(speriph_slave.add[5:2] == 4'ha)
                 begin
                    bbmux_sel_N = speriph_slave.wdata[0];
                 end
               else
                 begin
                      bbmux_N[speriph_slave.add[5:2]][1:0] = speriph_slave.wdata[1:0];
                   end
              end

            3'b001: // read bbmux
              begin
               r_data = { 30'h0 , bbmux_P[speriph_slave.add[5:2]][1:0]};
              end

            3'b010: // evnt mask and buffers handling
              begin
               for(int i=0; i< NUM_CORES; i++)
                 begin
                  //SET EVENT MASK
                  if ( speriph_slave.add[7:2] == 6'h0 + i )
                    begin
                     s_evnt_mask_low[i]   = speriph_slave.wdata;
                     evnt_mask_sel_low[i] = 1;
                    end
                  else if (speriph_slave.add[7:2] == 6'h10+i)
                    begin
                     s_evnt_mask_high[i]   = speriph_slave.wdata;
                     evnt_mask_sel_high[i] = 1;
                    end
                  //CLEAR BUFFER
                  else if (speriph_slave.add[7:2] == 6'h20+i)
                    begin
                     s_evnt_buffer_clear_low[i] = speriph_slave.wdata;

                    end
                  else if (speriph_slave.add[7:2] == 6'h30+i)
                    begin
                     s_evnt_buffer_clear_high[i] = speriph_slave.wdata;
                    end
                 end
              end

            3'b011: // read evnt mask and buffers
              begin
               for(int i=0; i< NUM_CORES; i++)
                 begin
                  //READ EVENT MASK
                  if ( speriph_slave.add[7:2] == 6'h0 + i )
                    begin
                     r_data = r_evnt_mask_low[i];
                    end
                  else if (speriph_slave.add[7:2] == 6'h10+i)
                    begin
                     r_data =  r_evnt_mask_high[i];
                    end
                  //READ BUFFER
                  else if (speriph_slave.add[7:2] == 6'h20+i)
                    begin
                     r_data = r_evnt_buffer_low[i]; //17 bits from buffers(16GP+1emergency) + 15 zeros
                    end
                  else if (speriph_slave.add[7:2] == 6'h30+i)
                    begin
                     r_data =  r_evnt_buffer_high[i];
                    end
                 end
              end

            3'b100:  //interrupts
              begin
               for(int i=0; i< NUM_CORES; i++)
                 begin
                  //SET INTERRUPTS MASK
                  if ( speriph_slave.add[7:2] == 6'h0 + i )
                    begin
                     s_interrupt_mask_low[i] = speriph_slave.wdata;
                     interrupt_mask_sel_low[i] = 1;
                    end
                  else if (speriph_slave.add[7:2] == 6'h10+i)
                    begin
                     s_interrupt_mask_high[i] = speriph_slave.wdata;
                     interrupt_mask_sel_high[i] = 1;
                    end
                  //CLEAR BUFFER
                  else if (speriph_slave.add[7:2] == 6'h20+i)
                    begin
                     s_interrupt_buffer_clear_low[i] = speriph_slave.wdata;

                    end
                  else if (speriph_slave.add[7:2] == 6'h30+i)
                    begin
                     s_interrupt_buffer_clear_high[i] = speriph_slave.wdata;

                    end
                 end
              end


            3'b101: //read interrupts mask and buffers
              begin
               for(int i=0; i< NUM_CORES; i++)
                 begin
                  //SET INTERRUPTS MASK
                  if ( speriph_slave.add[7:2] == 6'h0 + i )
                    begin
                     r_data =   r_interrupt_mask_low[i];
                    end
                  else if (speriph_slave.add[7:2] == 6'h10+i)
                    begin
                     r_data =  r_interrupt_mask_high[i];
                    end
                  //CLEAR BUFFER
                  else if (speriph_slave.add[7:2] == 6'h20+i)
                    begin
                     r_data =  r_interrupt_buffer_low[i];   //17 bits from buffers(16GP+1emergency) + 15 zeros
                    end
                  else if (speriph_slave.add[7:2] == 6'h30+i)
                    begin
                     r_data =  r_interrupt_buffer_high[i];
                    end
                 end
              end

            3'b110:
              begin
               case(speriph_slave.add[7:2])
                 6'h0:
                   begin
                    ClkGate_N[speriph_slave.wdata[3:0]] = 1;
                   end
                 6'h1:
                   begin
                    ClkGate_N[speriph_slave.wdata[3:0]] = 0;
                   end

                 6'h2:
                   begin
                      if(NUM_CORES == 1)
                      begin
                          s_clk_stop_o = 1;
                          s_clk_status = 1;
                      end
                      else
                      begin
                          s_clk_stop_o[speriph_slave.wdata[LOG_NUM_CORES-1:0]] = 1;
                          s_clk_status[speriph_slave.wdata[LOG_NUM_CORES-1:0]] = 1;
                      end
                   end

                 6'h3 :
                   begin
                    s_Emergency_event = speriph_slave.wdata[NUM_CORES-1:0];
                   end
                 6'h4 :
                   begin
                    s_Emergency_IRQ = speriph_slave.wdata[NUM_CORES-1:0];
                   end
                 6'h6 :
                   begin
                    s_emergency_interrupt_clear = speriph_slave.wdata[NUM_CORES-1:0];
                   end
                 6'h5 :
                   begin
                    s_emergency_evnt_clear = speriph_slave.wdata[NUM_CORES-1:0];
                   end
                 6'h17 :
                   begin
                    s_internal_event[0] = speriph_slave.wdata[(NUM_CORES)-1:0];    //same signals for both events and interrupts
                   end
                 6'h18:
                   begin
                    s_internal_event[1] = speriph_slave.wdata[(NUM_CORES)-1:0];     //same signals for both events and interrupts
                   end
                 6'h19:
                   begin
                    s_internal_event[2] = speriph_slave.wdata[(NUM_CORES)-1:0];     //same signals for both events and interrupts
                   end
                 6'h1A:
                   begin
                    s_internal_event[3] = speriph_slave.wdata[(NUM_CORES)-1:0];     //same signals for both events and interrupts
                   end
                 6'h1B :
                   begin
                    s_get_barrier[ speriph_slave.wdata[$clog2(6)-1:0] ]  = 1;//
                   end
                 6'h1C:
                   begin
                    s_clear_barrier_req[speriph_slave.wdata[$clog2(6)-1:0]] = 1;
                   end

`ifdef FEATURE_IDLE_CNT
               6'h23 :
                 begin
                  clear_cnt_o[ speriph_slave.wdata[LOG_NUM_CORES-1:0] ]  = 1;//

                 end
               6'h24 :
                 begin
                start_cnt_o = speriph_slave.wdata[NUM_CORES-1:0];
                 end
`endif
                 default:
                   begin
                    for ( int i = 0; i < 6 ; i++ )
                      begin
                         if( speriph_slave.add[7:2] == 6'h1D + i )
                           begin
                            s_barrier_mask_to_trigg[i] = speriph_slave.wdata[NUM_CORES-1:0];
                            s_barrier_num_threads[i] = speriph_slave.wdata[16+$clog2(NUM_CORES):16];
                            s_barrier_store[i] = 1'b1;
                           end
                      end
                   end
               endcase
              end

            3'b111:
              begin
               case(speriph_slave.add[7:2])
                 6'h0:
                   begin
                    r_data = {25'b0, ClkGate_P};
                   end
                 6'h2:
                   begin
                    r_data = { {(32-NUM_CORES){1'b0}},r_clk_status};
                   end
                 6'h3 :
                   begin
                    r_data = { {(32-NUM_CORES){1'b0}},Emergency_event_status_i};
                   end
                 6'h4 :
                   begin
                    r_data = { {(32-NUM_CORES){1'b0}},Emergency_interrupt_status_i};
                   end
                 default:
                   begin
                      for(int i=0; i< NUM_CORES; i++)
                        begin
                         if ( speriph_slave.add[7:2] == 6'h7 + i )
                           begin
                            r_data =  { 24'b0, IRQ_id[i] };
                           end
`ifdef FEATURE_IDLE_CNT
                         else if( speriph_slave.add[7:2] == 6'h24 + i )
                           begin
                            r_data =  idle_cyc_cnt_i[i];
                           end
`endif
                        end
                      for ( int i = 0; i < 6 ; i++ )
                        begin
                         if( speriph_slave.add[7:2] == 6'h1D + i )
                           begin
                            r_data =  Barrier_counter_i[i];
                           end
                        end
                   end
               endcase
              end
            endcase
           end
        end

      TRANS_REQ:
        begin
         // outputs
         speriph_slave.r_rdata = r_data_p;
         speriph_slave.r_valid = 1'b1;
         speriph_slave.r_id    = s_r_id;
         NS = TRANS_IDLE;

         if ( speriph_slave.req == 1'b1 )
           begin
            NS = TRANS_REQ;
            case({speriph_slave.add[9],speriph_slave.add[8],speriph_slave.wen})
            3'b000:
              begin
                 if(speriph_slave.add[5:2] == 4'ha)
                 begin
                    bbmux_sel_N = speriph_slave.wdata[0];
                 end
               else
                 begin
                      bbmux_N[speriph_slave.add[5:2]][1:0] = speriph_slave.wdata[1:0];
                   end
              end

            3'b001: // read bbmux
              begin
               r_data = { 30'h0 ,bbmux_P[speriph_slave.add[5:2]][1:0]};
              end

            3'b010: // set evnt mask or clear buffers
              begin
               for(int i=0; i< NUM_CORES; i++)
                 begin
                  //SET EVENT MASK
                  if ( speriph_slave.add[7:2] == 6'h0 + i )
                    begin
                     s_evnt_mask_low[i] = speriph_slave.wdata;
                     evnt_mask_sel_low[i] = 1;
                    end
                  else if (speriph_slave.add[7:2] == 6'h10+i)
                    begin
                     s_evnt_mask_high[i] = speriph_slave.wdata;
                     evnt_mask_sel_high[i] = 1;
                    end
                  //CLEAR BUFFER
                  else if (speriph_slave.add[7:2] == 6'h20+i)
                    begin
                     s_evnt_buffer_clear_low[i] = speriph_slave.wdata;

                    end
                  else if (speriph_slave.add[7:2] == 6'h30+i)
                    begin
                     s_evnt_buffer_clear_high[i] = speriph_slave.wdata;
                    end
                 end
              end

            3'b011: // read evnt mask and buffers
              begin
               for(int i=0; i< NUM_CORES; i++)
                 begin
                  //READ EVENT MASK
                  if ( speriph_slave.add[7:2] == 6'h0 + i )
                    begin
                     r_data =  r_evnt_mask_low[i];
                    end
                  else if (speriph_slave.add[7:2] == 6'h10+i)
                    begin
                     r_data =  r_evnt_mask_high[i];
                    end
                  //CLEAR BUFFER
                  else if (speriph_slave.add[7:2] == 6'h20+i)
                    begin
                     r_data =  r_evnt_buffer_low[i]; //17 bits from buffers(16GP+1emergency) + 15 zeros
                    end
                  else if (speriph_slave.add[7:2] == 6'h30+i)
                    begin
                     r_data =  r_evnt_buffer_high[i];
                    end
                 end
              end

            3'b100:  //interrupts
              begin
               for(int i=0; i< NUM_CORES; i++)
                 begin
                  //SET INTERRUPTS MASK
                  if ( speriph_slave.add[7:2] == 6'h0 + i )
                    begin
                     s_interrupt_mask_low[i] = speriph_slave.wdata;
                     interrupt_mask_sel_low[i] = 1;
                    end
                  else if (speriph_slave.add[7:2] == 6'h10+i)
                    begin
                     s_interrupt_mask_high[i] = speriph_slave.wdata;
                     interrupt_mask_sel_high[i] = 1;
                    end
                  //CLEAR BUFFER
                  else if (speriph_slave.add[7:2] == 6'h20+i)
                    begin
                     s_interrupt_buffer_clear_low[i] = speriph_slave.wdata;

                    end
                  else if (speriph_slave.add[7:2] == 6'h30+i)
                    begin
                     s_interrupt_buffer_clear_high[i] = speriph_slave.wdata;

                    end
                 end
              end


            3'b101: //read interrupts mask and buffers
              begin
               for(int i=0; i< NUM_CORES; i++)
                 begin
                  //READ INTERRUPTS MASK
                  if ( speriph_slave.add[7:2] == 6'h0 + i )
                    begin
                     r_data =  r_interrupt_mask_low[i];
                    end
                  else if (speriph_slave.add[7:2] == 6'h10+i)
                    begin
                     r_data =  r_interrupt_mask_high[i];
                    end
                  //READ BUFFER
                  else if (speriph_slave.add[7:2] == 6'h20+i)
                    begin
                     r_data =  r_interrupt_buffer_low[i]; //17 bits from buffers(16GP+1emergency) + 15 zeros
                    end
                  else if (speriph_slave.add[7:2] == 6'h30+i)
                    begin
                     r_data =  r_interrupt_buffer_high[i];
                    end
                 end
              end

            3'b110:
              begin
               case(speriph_slave.add[7:2])
                 6'h0:
                   begin
                    ClkGate_N[speriph_slave.wdata[3:0]] = 1;
                   end
                 6'h1:
                   begin
                    ClkGate_N[speriph_slave.wdata[3:0]] = 0;
                   end

                 6'h2:
                   begin
                    if(NUM_CORES == 1)
                    begin
                        s_clk_stop_o = 1;
                        s_clk_status = 1;
                    end
                    else
                    begin
                        s_clk_stop_o[speriph_slave.wdata[LOG_NUM_CORES-1:0]] = 1;
                        s_clk_status[speriph_slave.wdata[LOG_NUM_CORES-1:0]] = 1;
                    end
                   end

                 6'h3 :
                   begin
                    s_Emergency_event = speriph_slave.wdata[NUM_CORES-1:0];
                   end
                 6'h4 :
                   begin
                    s_Emergency_IRQ = speriph_slave.wdata[NUM_CORES-1:0];
                   end
                 6'h6 :
                   begin
                    s_emergency_interrupt_clear = speriph_slave.wdata[NUM_CORES-1:0];
                   end
                 6'h5 :
                   begin
                    s_emergency_evnt_clear = speriph_slave.wdata[NUM_CORES-1:0];
                   end
                 6'h17 :
                   begin
                    s_internal_event[0] = speriph_slave.wdata[(NUM_CORES)-1:0];    //same signals for both events and interrupts
                   end
                 6'h18:
                   begin
                    s_internal_event[1] = speriph_slave.wdata[(NUM_CORES)-1:0];     //same signals for both events and interrupts
                   end
                 6'h19:
                   begin
                    s_internal_event[2] = speriph_slave.wdata[(NUM_CORES)-1:0];     //same signals for both events and interrupts
                   end
                 6'h1A:
                   begin
                    s_internal_event[3] = speriph_slave.wdata[(NUM_CORES)-1:0];     //same signals for both events and interrupts
                   end
                 6'h1B :
                   begin
                    s_get_barrier[ speriph_slave.wdata[$clog2(6)-1:0] ]  = 1;//

                   end
                 6'h1C:
                   begin
                    s_clear_barrier_req[speriph_slave.wdata[$clog2(6)-1:0]] = 1;
                   end
`ifdef FEATURE_IDLE_CNT
                 6'h23 :
                   begin
                    clear_cnt_o[ speriph_slave.wdata[LOG_NUM_CORES-1:0] ]  = 1;//

                   end
                 6'h24 :
                   begin
                  start_cnt_o = speriph_slave.wdata[NUM_CORES-1:0];
                   end
`endif
                 default:
                   begin
                    for ( int i = 0; i < 6 ; i++ )
                      begin
                         if( speriph_slave.add[7:2] == 6'h1D + i )
                           begin
                            s_barrier_mask_to_trigg[i] = speriph_slave.wdata[NUM_CORES-1:0];
                            s_barrier_num_threads[i] = speriph_slave.wdata[16+$clog2(NUM_CORES):16];
                            s_barrier_store[i] = 1'b1;
                           end
                      end
                   end
               endcase
              end

            3'b111:
              begin
               case(speriph_slave.add[7:2])
                 6'h0:
                   begin
                    r_data = { {(25){1'b0}},ClkGate_P};
                   end
                 6'h2:
                   begin
                    r_data = { {(32-NUM_CORES){1'b0}},r_clk_status};
                   end
                 6'h3 :
                   begin
                    r_data = { {(32-NUM_CORES){1'b0}},Emergency_event_status_i};
                   end
                 6'h4 :
                   begin
                    r_data = { {(32-NUM_CORES){1'b0}},Emergency_interrupt_status_i};
                   end
                 default:
                   begin
                      for(int i=0; i< NUM_CORES; i++)
                        begin
                         if ( speriph_slave.add[7:2] == 6'h7 + i )
                           begin
                            r_data =  { {24{1'b0}}, IRQ_id[i] };
                           end
`ifdef FEATURE_IDLE_CNT
                         else if( speriph_slave.add[7:2] == 6'h24 + i )
                           begin
                            r_data =  idle_cyc_cnt_i[i];
                           end
`endif
                        end
                    for ( int i = 0; i < 6 ; i++ )
                      begin
                         if( speriph_slave.add[7:2] == 6'h1D + i )
                           begin
                            r_data =  Barrier_counter_i[i];
                           end
                      end

                   end
               endcase
              end
            endcase
           end
        end
      endcase
     end











   //REGISTER TO GENERATE R_ID
   always_ff @(posedge clk_i, negedge rst_ni)
     begin
      if (rst_ni == 1'b0)
        begin
           s_r_id   <= '0;
           r_data_p <= 'b0;
           CS <= TRANS_IDLE;
        end
      else
        begin
           s_r_id <= speriph_slave.id;
           r_data_p <= r_data;
           CS <= NS;
        end
     end

   //**********************************************************
   //*************** CLK GATE/ BBMUX REGISTERS ****************
   //**********************************************************

   always_ff @(posedge clk_i, negedge rst_ni)
     begin
        if (~rst_ni)
          begin
           ClkGate_P    <= 7'b0;
           bbmux_P      <= {10{2'b0}};
           bbmux_sel_P  <= 1'b0;
           r_clk_status <= '0;  //lets keep this register...in this way as soon the stop signal is generated, the core will be seen as sleeping.
        end
        else
          begin
           ClkGate_P <= ClkGate_N;
           bbmux_P <= bbmux_N;
           bbmux_sel_P <= bbmux_sel_N;
           r_clk_status <= s_clk_status;
           for( int i = 0; i < NUM_CORES; i++ ) begin
              if ( r_event_detect_i[i] == 1 ) begin
                 r_clk_status[i] <= 0;
              end
           end
          end
     end


   //**********
   // Fixed priority arbiter + id encoder
   //**********
   generate
      for( i=0; i< NUM_CORES; i++)
      begin : FIX_PRI
          interrupt_id_arbiter
          #(
               .NUM_CORES(NUM_CORES)
          )
          interrupt_id_arbiter_i
          (
                 .interrupt_buffer_status_i(interrupt_buffer_status[i]),
                 .IRQ_id_o                 (IRQ_id[i]                 )
          );
      end
   endgenerate


   //**********************************************************
   //*************** BINDING OF OUTPUT SIGNALS  ***************
   //**********************************************************

   assign speriph_slave.r_opc = 1'b0;
   // clkgate
   assign r_clkgate_P[3:0] = ClkGate_P[3:0];
   assign r_clkgate_P[4]   = ClkGate_P[4];
   assign r_clkgate_P[5]   = ClkGate_P[5];
   assign r_clkgate_P[6]   = ClkGate_P[6];
   //bbmux
   // FIXME ONLY 4 cores supported
   assign bbmux_bus.bbmux_tcdm    = bbmux_P[0];
   assign bbmux_bus.bbmux_core[0] = bbmux_P[4];
   assign bbmux_bus.bbmux_core[1] = bbmux_P[5];
   assign bbmux_bus.bbmux_core[2] = bbmux_P[6];
   assign bbmux_bus.bbmux_core[3] = bbmux_P[7];
   assign bbmux_bus.bbmux_int     = bbmux_P[8];
   assign bbmux_bus.bbmux_scm     = bbmux_P[9];
   assign bbmux_bus.bbmux_sel     = bbmux_sel_P;

endmodule
