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

/// A simple two channel interface.
///
/// This interface provides two channels, one for requests and one for
/// responses. Both channels have a valid/ready handshake. The sender sets the
/// channel signals and pulls valid high. Once pulled high, valid must remain
/// high and none of the signals may change. The transaction completes when both
/// valid and ready are high. Valid must not depend on ready. The master can
/// request a read or write on the `q` channel. The slave responds on the `p`
/// channel once the action has been completed.
interface REQRSP_BUS #(
  /// The width of the address.
  parameter int ADDR_WIDTH = -1,
  /// The width of the data.
  parameter int DATA_WIDTH = -1,
  /// The width of the ID.
  parameter int ID_WIDTH = -1
)(
  input logic clk_i
);

  // The request channel (Q).
  logic [ADDR_WIDTH-1:0]   qaddr;
  logic                    qwrite; // 0=read, 1=write
  logic [DATA_WIDTH-1:0]   qdata;
  logic [DATA_WIDTH/8-1:0] qstrb;  // byte-wise strobe
  logic [ID_WIDTH-1:0]     qid;
  logic                    qvalid;
  logic                    qready;

  // The response channel (P).
  logic [DATA_WIDTH-1:0]   pdata;
  logic                    perror; // 0=ok, 1=error
  logic [ID_WIDTH-1:0]     pid;
  logic                    pvalid;
  logic                    pready;

  modport in  (input  qaddr, qwrite, qdata, qstrb, qid, qvalid, pready, output qready, pdata, perror, pid, pvalid);
  modport out (output qaddr, qwrite, qdata, qstrb, qid, qvalid, pready, input  qready, pdata, perror, pid, pvalid);

endinterface
