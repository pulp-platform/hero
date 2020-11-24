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

/// A protocol adapter from REQRSP to TCDM.
module reqrsp_to_tcdm #(
    /// The address width. >=1.
    parameter int AW = -1,
    /// The data width. >=1.
    parameter int DW = -1,
    /// The ID width. >=0.
    parameter int IW = -1,
    /// The number of TCDM requests that can be in flight at most. >=1.
    parameter int NUM_PENDING = 2
)(
    input  logic            clk_i        ,
    input  logic            rst_ni       ,

    REQRSP_BUS.in           reqrsp_i     ,

    output logic [AW-1:0]   tcdm_add     ,
    output logic            tcdm_wen     ,
    output logic [DW-1:0]   tcdm_wdata   ,
    output logic [DW/8-1:0] tcdm_be      ,
    output logic            tcdm_req     ,
    input  logic            tcdm_gnt     ,
    input  logic [DW-1:0]   tcdm_r_rdata ,
    input  logic            tcdm_r_valid
);

    // Check invariants.
    `ifndef SYNTHESIS
    initial begin
        assert(AW > 0);
        assert(DW > 0);
        assert(IW >= 0);
        assert(NUM_PENDING > 0);
        assert(reqrsp_i.ADDR_WIDTH == AW);
        assert(reqrsp_i.DATA_WIDTH == DW);
        assert(reqrsp_i.ID_WIDTH   == IW);
    end
    `endif

    // The request counter makes sure that at most NUM_PENDING requests are in
    // flight simultaneously. This ensures that the queue can always capture all
    // responses.
    localparam int W = $clog2(NUM_PENDING+1);
    logic [W-1:0] count_q, count_d;

    always_ff @(posedge clk_i, negedge rst_ni) begin : ps_count
        if (!rst_ni)
            count_q <= '0;
        else
            count_q <= count_d;
    end

    always_comb begin : pc_count
        count_d = count_q;
        if (reqrsp_i.qvalid && reqrsp_i.qready)
            count_d++;
        if (reqrsp_i.pvalid && reqrsp_i.pready)
            count_d--;
    end

    // Stall the incoming requests if too many requests are pending.
    always_comb begin : p_req
        tcdm_add   = reqrsp_i.qaddr;
        tcdm_wen   = reqrsp_i.qwrite;
        tcdm_wdata = reqrsp_i.qdata;
        tcdm_be    = reqrsp_i.qstrb;
        if (count_q == NUM_PENDING) begin
            tcdm_req = 0;
            reqrsp_i.qready = 0;
        end else begin
            tcdm_req = reqrsp_i.qvalid;
            reqrsp_i.qready = tcdm_gnt;
        end
    end

    // The ID queue holds the IDs that were provided with a request. These are
    // then used to annotate the responses with the correct ID again.
    fifo #(
        .DEPTH        ( NUM_PENDING ),
        .DATA_WIDTH   ( IW          ),
        .FALL_THROUGH ( 1           )
    ) i_id_queue (
        .clk_i       ( clk_i                              ),
        .rst_ni      ( rst_ni                             ),
        .flush_i     ( 1'b0                               ),
        .testmode_i  ( 1'b0                               ),
        .full_o      (                                    ),
        .empty_o     (                                    ),
        .threshold_o (                                    ),
        .data_i      ( reqrsp_i.qid                       ),
        .push_i      ( reqrsp_i.qready && reqrsp_i.qvalid ),
        .data_o      ( reqrsp_i.pid                       ),
        .pop_i       ( reqrsp_i.pready && reqrsp_i.pvalid )
    );

    // The response queue holds the responses as they come back from the TCDM.
    logic queue_full;
    logic queue_empty;

    fifo #(
        .DEPTH        ( NUM_PENDING ),
        .DATA_WIDTH   ( DW          ),
        .FALL_THROUGH ( 1           )
    ) i_rsp_queue (
        .clk_i       ( clk_i                              ),
        .rst_ni      ( rst_ni                             ),
        .flush_i     ( 1'b0                               ),
        .testmode_i  ( 1'b0                               ),
        .full_o      ( queue_full                         ),
        .empty_o     ( queue_empty                        ),
        .threshold_o (                                    ),
        .data_i      ( tcdm_r_rdata                       ),
        .push_i      ( tcdm_r_valid                       ),
        .data_o      ( reqrsp_i.pdata                     ),
        .pop_i       ( reqrsp_i.pready && reqrsp_i.pvalid )
    );

    always_comb begin : p_rsp
        reqrsp_i.perror = 0;
        reqrsp_i.pvalid = !queue_empty;
    end

    // The queue should never fill up, as this is prevented by the counter in
    // the request path.
    // pragma translate_off
    `ifndef VERILATOR
    assert property (@(posedge clk_i) tcdm_r_valid |-> !queue_full);
    `endif
    // pragma translate_on

endmodule
