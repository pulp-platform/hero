// Copyright (c) 2017-2018 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

/// A set of testbench utilities for REQRSP interfaces.
package reqrsp_test;

  /// A driver for the REQRSP interface.
  class reqrsp_driver #(
    parameter int  AW = -1,
    parameter int  DW = -1,
    parameter int  IW = -1,
    parameter time TA = 0 , // stimuli application time
    parameter time TT = 0   // stimuli test time
  );
    virtual REQRSP_BUS #(
      .ADDR_WIDTH(AW),
      .DATA_WIDTH(DW),
      .ID_WIDTH(IW)
    ) bus;

    function new(
      virtual REQRSP_BUS #(
        .ADDR_WIDTH(AW),
        .DATA_WIDTH(DW),
        .ID_WIDTH(IW)
      ) bus
    );
      this.bus = bus;
    endfunction

    task reset_master;
      bus.qaddr  <= '0;
      bus.qwrite <= '0;
      bus.qdata  <= '0;
      bus.qstrb  <= '0;
      bus.qid    <= '0;
      bus.qvalid <= '0;
      bus.pready <= '0;
    endtask

    task reset_slave;
      bus.qready <= '0;
      bus.pdata  <= '0;
      bus.perror <= '0;
      bus.pid    <= '0;
      bus.pvalid <= '0;
    endtask

    task cycle_start;
      #TT;
    endtask

    task cycle_end;
      @(posedge bus.clk_i);
    endtask

    /// Send a request.
    task send_req (
      input logic [AW-1:0]   addr  ,
      input logic            write ,
      input logic [DW-1:0]   data  ,
      input logic [DW/8-1:0] strb  ,
      input logic [IW-1:0]   id
    );
      bus.qaddr  <= #TA addr;
      bus.qwrite <= #TA write;
      bus.qdata  <= #TA data;
      bus.qstrb  <= #TA strb;
      bus.qid    <= #TA id;
      bus.qvalid <= #TA 1;
      cycle_start();
      while (bus.qready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      bus.qaddr  <= #TA '0;
      bus.qwrite <= #TA '0;
      bus.qdata  <= #TA '0;
      bus.qstrb  <= #TA '0;
      bus.qid    <= #TA '0;
      bus.qvalid <= #TA 0;
    endtask

    /// Send a response.
    task send_rsp (
      input logic [DW-1:0] data  ,
      input logic          error ,
      input logic [IW-1:0] id
    );
      bus.pdata  <= #TA data;
      bus.perror <= #TA error;
      bus.pid    <= #TA id;
      bus.pvalid <= #TA 1;
      cycle_start();
      while (bus.pready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      bus.pdata  <= #TA '0;
      bus.perror <= #TA '0;
      bus.pid    <= #TA '0;
      bus.pvalid <= #TA 0;
    endtask

    /// Receive a request.
    task recv_req (
      output logic [AW-1:0]   addr  ,
      output logic            write ,
      output logic [DW-1:0]   data  ,
      output logic [DW/8-1:0] strb  ,
      output logic [IW-1:0]   id
    );
      bus.qready <= #TA 1;
      cycle_start();
      while (bus.qvalid != 1) begin cycle_end(); cycle_start(); end
      addr  = bus.qaddr;
      write = bus.qwrite;
      data  = bus.qdata;
      strb  = bus.qstrb;
      id    = bus.qid;
      cycle_end();
      bus.qready <= #TA 0;
    endtask

    /// Receive a response.
    task recv_rsp (
      output logic [DW-1:0] data  ,
      output logic          error ,
      output logic [IW-1:0] id
    );
      bus.pready <= #TA 1;
      cycle_start();
      while (bus.pvalid != 1) begin cycle_end(); cycle_start(); end
      data  = bus.pdata;
      error = bus.perror;
      id    = bus.pid;
      cycle_end();
      bus.pready <= #TA 0;
    endtask

  endclass

endpackage
