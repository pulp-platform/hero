// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


// jtag_test.sv
// Francesco Conti <fconti@iis.ee.ethz.ch>
// Antonio Pullini <pullinia@iis.ee.ethz.ch>
// Robert Balas <balasr@iis.ee.ethz.ch>

// A set of testbench utilities for jtag

// It's best that you don't read below this line
// ---------------------------------------------
package jtag_test;

   parameter int unsigned JTAG_SOC_INSTR_WIDTH                                 = 5;
   parameter logic [JTAG_SOC_INSTR_WIDTH-1:0]  JTAG_SOC_IDCODE                 = 5'b00001;
   parameter logic [JTAG_SOC_INSTR_WIDTH-1:0]  JTAG_SOC_DTMCSR                 = 5'b10000;
   parameter logic [JTAG_SOC_INSTR_WIDTH-1:0]  JTAG_SOC_DMIACCESS              = 5'b10001;
   parameter logic [JTAG_SOC_INSTR_WIDTH-1:0]  JTAG_SOC_AXIREG                 = 5'b00100;
   parameter logic [JTAG_SOC_INSTR_WIDTH-1:0]  JTAG_SOC_BBMUXREG               = 5'b00101;
   parameter logic [JTAG_SOC_INSTR_WIDTH-1:0]  JTAG_SOC_CONFREG                = 5'b00110;
   parameter logic [JTAG_SOC_INSTR_WIDTH-1:0]  JTAG_SOC_TESTMODEREG            = 5'b01000;
   parameter logic [JTAG_SOC_INSTR_WIDTH-1:0]  JTAG_SOC_BISTREG                = 5'b01001;
   parameter logic [JTAG_SOC_INSTR_WIDTH-1:0]  JTAG_SOC_BYPASS                 = 5'b11111;
   parameter int unsigned JTAG_SOC_IDCODE_WIDTH                                = 32;
   parameter int unsigned JTAG_SOC_BBMUXREG_WIDTH                              = 21;
   parameter int unsigned JTAG_SOC_CLKGATEREG_WIDTH                            = 11;
   parameter int unsigned JTAG_SOC_CONFREG_WIDTH                               = 16;
   parameter int unsigned JTAG_SOC_TESTMODEREG_WIDTH                           =  4;
   parameter int unsigned JTAG_SOC_BISTREG_WIDTH                               = 20;

   parameter int unsigned JTAG_CLUSTER_INSTR_WIDTH                             = 5;
   parameter logic [JTAG_CLUSTER_INSTR_WIDTH-1:0]  JTAG_CLUSTER_IDCODE         = 5'b0010;
   parameter logic [JTAG_CLUSTER_INSTR_WIDTH-1:0]  JTAG_CLUSTER_SAMPLE_PRELOAD = 5'b0001;
   parameter logic [JTAG_CLUSTER_INSTR_WIDTH-1:0]  JTAG_CLUSTER_EXTEST         = 5'b0000;
   parameter logic [JTAG_CLUSTER_INSTR_WIDTH-1:0]  JTAG_CLUSTER_DEBUG          = 5'b1000;
   parameter logic [JTAG_CLUSTER_INSTR_WIDTH-1:0]  JTAG_CLUSTER_MBIST          = 5'b1001;
   parameter logic [JTAG_CLUSTER_INSTR_WIDTH-1:0]  JTAG_CLUSTER_BYPASS         = 5'b1111;
   parameter int unsigned JTAG_CLUSTER_IDCODE_WIDTH                            = 32;

   parameter int unsigned JTAG_IDCODE_WIDTH                                    = JTAG_SOC_IDCODE_WIDTH;
   parameter int unsigned JTAG_INSTR_WIDTH                                     = JTAG_SOC_INSTR_WIDTH;

   parameter DMI_SIZE = 32+7+2;

   //parameter time          TCK_PERIOD = 100ns;
   parameter time          TCK_PERIOD = 10ns;
   /// A driver for JTAG ports

   task automatic jtag_wait_halfperiod(input int cycles);
     #(TCK_PERIOD/2);
   endtask

   task automatic jtag_clock(
      input int cycles,
      ref logic s_tck
   );
      for(int i=0; i<cycles; i=i+1) begin
         s_tck = 1'b0;
         jtag_wait_halfperiod(1);
         s_tck = 1'b1;
         jtag_wait_halfperiod(1);
         s_tck = 1'b0;
      end
   endtask

   task automatic jtag_reset(
      ref logic s_tck,
      ref logic s_tms,
      ref logic s_trstn,
      ref logic s_tdi
   );
      s_tms   = 1'b0;
      s_tck   = 1'b0;
      s_trstn = 1'b0;
      s_tdi   = 1'b0;
      jtag_wait_halfperiod(2);
      s_trstn = 1'b1;
   endtask

   task automatic jtag_softreset(
      ref logic s_tck,
      ref logic s_tms,
      ref logic s_trstn,
      ref logic s_tdi
   );
      s_tms   = 1'b1;
      s_trstn = 1'b1;
      s_tdi   = 1'b0;
      jtag_clock(5, s_tck); //enter RST
      s_tms   = 1'b0;
      jtag_clock(1, s_tck); // back to IDLE
      $display("[JTAG] %t - soft reset", $realtime);

   endtask

   class JTAG_reg #(int unsigned size = 32, logic [(JTAG_CLUSTER_INSTR_WIDTH+JTAG_SOC_INSTR_WIDTH)-1:0] instr = 'h0);

      task idle(
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi
      );
         s_trstn = 1'b1;
         // from SHIFT_DR to RUN_TEST : tms sequence 10
         s_tms   = 1'b1;
         s_tdi   = 1'b0;
         jtag_clock(1, s_tck);
         s_tms   = 1'b0;
         jtag_clock(1, s_tck);
      endtask

      task update_and_goto_shift(
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi
      );
         s_trstn = 1'b1;
         // from SHIFT_DR to RUN_TEST : tms sequence 110
         s_tms   = 1'b1;
         s_tdi   = 1'b0;
         jtag_clock(1, s_tck);
         s_tms   = 1'b1;
         jtag_clock(1, s_tck);
         s_tms   = 1'b0;
         jtag_clock(1, s_tck);
         jtag_clock(1, s_tck);
      endtask

      task jtag_goto_SHIFT_IR(
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi
      );
         s_trstn = 1'b1;
         s_tdi   = 1'b0;
         // from IDLE to SHIFT_IR : tms sequence 1100
         s_tms   = 1'b1;
         jtag_clock(2, s_tck);
         s_tms   = 1'b0;
         jtag_clock(2, s_tck);
      endtask

      task jtag_goto_SHIFT_DR(
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi
      );
         s_trstn = 1'b1;
         s_tdi   = 1'b0;
         // from IDLE to SHIFT_IR : tms sequence 100
         s_tms   = 1'b1;
         jtag_clock(1, s_tck);
         s_tms   = 1'b0;
         jtag_clock(2, s_tck);
      endtask

      task jtag_goto_UPDATE_DR_FROM_SHIFT_DR(
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi
      );
         //$display("I am at jtag_goto_UPDATE_DR_FROM_SHIFT_DR (%t)",$realtime);
         s_trstn = 1'b1;
         s_tdi   = 1'b1;
         // from SHIFT DR to UPDATE DR : tms sequence 11
         s_tms   = 1'b1;
         jtag_clock(1, s_tck);
         // back to Idle : tms sequence 0
         s_tms   = 1'b0;
         //wait a bit
         jtag_clock(50, s_tck);
      endtask

      task jtag_goto_CAPTURE_DR_FROM_UPDATE_DR_GETDATA(
         output logic [DMI_SIZE-1:0] dataout,
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi,
         ref logic s_tdo
      );
         //$display("I am at jtag_goto_CAPTURE_DR_FROM_UPDATE_DR_GETDATA (%t)",$realtime);
         s_trstn = 1'b1;
         s_tdi   = 1'b1;
         // from UPDATE DR to CAPTURE DR : tms sequence 10
         s_tms   = 1'b1;
         jtag_clock(1, s_tck);
         s_tms   = 1'b0;
         jtag_clock(1, s_tck);
         //back to Idle: tms sequence 110
         s_tms   = 1'b1;
         jtag_clock(2, s_tck);
         s_tms   = 1'b0;
         jtag_clock(1, s_tck);
         // go to SHIFT DR: tms sequence 100
         s_tms   = 1'b1;
         jtag_clock(1, s_tck);
         s_tms   = 1'b0;
         jtag_clock(2, s_tck);
         s_tms   = 1'b0;
         for(int i=0; i<DMI_SIZE; i=i+1) begin
            if (i == (DMI_SIZE-1))
               s_tms = 1'b1;
            s_tdi = 1'b0;
            jtag_clock(1, s_tck);
            dataout[i] = s_tdo;
         end

      endtask

      task jtag_goto_CAPTURE_DR_FROM_SHIFT_DR_GETDATA(
         output logic [DMI_SIZE-1:0] dataout,
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi,
         ref logic s_tdo
      );
         //$display("I am at jtag_goto_CAPTURE_DR_FROM_SHIFT_DR_GETDATA (%t)",$realtime);
         s_trstn = 1'b1;
         s_tdi   = 1'b1;
         // from UPDATE DR to CAPTURE DR : tms sequence 110
         s_tms   = 1'b1;
         jtag_clock(2, s_tck);
         s_tms   = 1'b0;
         jtag_clock(1, s_tck);
         // go to SHIFT DR
         s_tms   = 1'b0;
         jtag_clock(1, s_tck);
         s_tms   = 1'b0;
         for(int i=0; i<DMI_SIZE; i=i+1) begin
            if (i == (DMI_SIZE-1))
               s_tms = 1'b1;
            s_tdi = 1'b0;
            jtag_clock(1, s_tck);
            dataout[i] = s_tdo;
         end

      endtask

      task jtag_shift_SHIFT_IR(
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi
      );
         s_trstn = 1'b1;
         s_tms   = 1'b0;
         for(int i=0; i<JTAG_SOC_INSTR_WIDTH; i=i+1) begin //TODO: generalize
            if (i==(JTAG_SOC_INSTR_WIDTH-1))
                 s_tms = 1'b1;
            s_tdi = instr[i];
            jtag_clock(1, s_tck);
         end
      endtask

      task jtag_shift_NBITS_SHIFT_DR (
         input int unsigned     numbits,
         input logic[size-1:0]  datain,
         output logic[size-1:0] dataout,
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi,
         ref logic s_tdo
      );
         s_trstn = 1'b1;
         s_tms   = 1'b0;
         for(int i=0; i<numbits; i=i+1) begin
            if (i == (numbits-1))
               s_tms = 1'b1;
            s_tdi = datain[i];
            jtag_clock(1, s_tck);
            dataout[i] = s_tdo;
         end
      endtask

      task shift_nbits_noex(
         input int unsigned     numbits,
         input logic[size-1:0]  datain,
         output logic[size-1:0] dataout,
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi,
         ref logic s_tdo
      );
         s_trstn = 1'b1;
         s_tms   = 1'b0;
         for(int i=0; i<numbits; i=i+1) begin
            s_tdi = datain[i];
            jtag_clock(1, s_tck);
            dataout[i] = s_tdo;
         end
      endtask

      task start_shift(
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi
      );
         this.jtag_goto_SHIFT_DR(s_tck, s_tms, s_trstn, s_tdi);
      endtask

      task shift_nbits(
         input int unsigned     numbits,
         input logic[size-1:0]  datain,
         output logic[size-1:0] dataout,
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi,
         ref logic s_tdo
      );
           this.jtag_shift_NBITS_SHIFT_DR(numbits, datain, dataout, s_tck, s_tms, s_trstn, s_tdi, s_tdo);
      endtask

      task setIR(
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi
      );
         this.jtag_goto_SHIFT_IR(s_tck, s_tms, s_trstn, s_tdi);
         this.jtag_shift_SHIFT_IR(s_tck, s_tms, s_trstn, s_tdi);
         this.idle(s_tck, s_tms, s_trstn, s_tdi);
      endtask

      task shift(
         input logic[size-1:0]  datain,
         output logic[size-1:0] dataout,
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi,
         ref logic s_tdo
      );
         this.jtag_goto_SHIFT_DR(s_tck, s_tms, s_trstn, s_tdi);
         this.jtag_shift_NBITS_SHIFT_DR(size, datain, dataout, s_tck, s_tms, s_trstn, s_tdi, s_tdo);
         this.idle(s_tck, s_tms, s_trstn, s_tdi);
      endtask

   endclass


   class test_mode_if_t;

      task init(
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi
      );
         JTAG_reg #(.size(256), .instr({JTAG_SOC_BYPASS, JTAG_SOC_CONFREG})) jtag_soc_dbg = new;
         jtag_soc_dbg.setIR(s_tck, s_tms, s_trstn, s_tdi);
         $display("[test_mode_if] %t - Init", $realtime);
      endtask

      task set_confreg(
         input  logic [8:0] confreg,
         output logic [8:0] dataout,
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi,
         ref logic s_tdo
      );
         logic [8+1:0] confreg_int, dataout_int; //extra bit for bypass
         JTAG_reg #(.size(256), .instr({JTAG_SOC_BYPASS, JTAG_SOC_CONFREG})) jtag_soc_dbg = new;

         confreg_int = {1'b0, confreg};

         jtag_soc_dbg.start_shift(s_tck, s_tms, s_trstn, s_tdi);
         jtag_soc_dbg.shift_nbits(9+1, confreg_int, dataout_int, s_tck, s_tms, s_trstn, s_tdi, s_tdo);
         jtag_soc_dbg.idle(s_tck, s_tms, s_trstn, s_tdi);
         dataout = dataout_int[8:0];
         $display("[test_mode_if] %t - Setting confreg to value %X.", $realtime, confreg);
      endtask

      task get_confreg(
         input logic [8:0] confreg,
         output bit  [8:0] rec,
         ref logic s_tck,
         ref logic s_tms,
         ref logic s_trstn,
         ref logic s_tdi,
         ref logic s_tdo
      );
         logic [8+1:0] dataout; //extra bit for bypass
         JTAG_reg #(.size(256), .instr({JTAG_SOC_BYPASS, JTAG_SOC_CONFREG})) jtag_soc_dbg = new;
         jtag_soc_dbg.start_shift(s_tck, s_tms, s_trstn, s_tdi);
         jtag_soc_dbg.shift_nbits(9+1, confreg, dataout, s_tck, s_tms, s_trstn, s_tdi, s_tdo);
         jtag_soc_dbg.idle(s_tck, s_tms, s_trstn, s_tdi);
         rec = dataout [8:0];
         // `DEBUG_MANAGER_INST.printf(STDOUT, 0, $sformatf("%s[TEST_MODE_IF] %s%t - %sGet confreg value = %X%s\n", `ESC_BLUE_BOLD, `ESC_WHITE, $realtime, `ESC_MAGENTA, rec, `ESC_DEFAULT));
      endtask

   endclass


endpackage

// Local Variables:
// verilog-indent-level: 3
// End:
