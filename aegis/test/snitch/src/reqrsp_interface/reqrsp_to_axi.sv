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

/// A protocol adapter from REQRSP to AXI4.
module reqrsp_to_axi #(
    /// The address width of the REQRSP bus. >=1.
    parameter int IN_AW = -1,
    /// The data width of the REQRSP bus. >=1.
    parameter int IN_DW = -1,
    /// The ID width of the REQRSP bus. >=0.
    parameter int IN_IW = -1,
    /// The address width of the AXI bus. >=1.
    parameter int OUT_AW = -1,
    /// The data width of the AXI bus. >=1.
    parameter int OUT_DW = -1,
    /// The ID width of the AXI bus. >=0.
    parameter int OUT_IW = -1,
    /// The user data width of the AXI bus. >=0.
    parameter int OUT_UW = -1,
    /// The number of reads that may be pending at any time.
    parameter int NUM_PENDING = 4
)(
    input logic    clk_i,
    input logic    rst_ni,
    REQRSP_BUS.in  reqrsp_i,
    AXI_BUS.Master axi_o
);

    localparam IN_ALIGN   = $clog2(IN_DW/8);
    localparam OUT_ALIGN  = $clog2(OUT_DW/8);
    localparam ALIGN_DIFF_REQ = IN_ALIGN > OUT_ALIGN ? IN_ALIGN-OUT_ALIGN : 0;
    localparam ALIGN_DIFF_RSP = OUT_ALIGN > IN_ALIGN ? OUT_ALIGN-IN_ALIGN : 0;

    // Check invariants.
    `ifndef SYNTHESIS
    initial begin
        assert(IN_AW  >  0);
        assert(IN_DW  >  0);
        assert(IN_IW  >= 0);
        assert(OUT_AW >  0);
        assert(OUT_DW >  0);
        assert(OUT_IW >= 0);
        assert(OUT_UW >= 0);
        assert(axi_o.AXI_ADDR_WIDTH == OUT_AW);
        assert(axi_o.AXI_DATA_WIDTH == OUT_DW);
        assert(axi_o.AXI_ID_WIDTH   == OUT_IW);
        assert(axi_o.AXI_USER_WIDTH == OUT_UW);
        assert(reqrsp_i.ADDR_WIDTH  == IN_AW);
        assert(reqrsp_i.DATA_WIDTH  == IN_DW);
        assert(reqrsp_i.ID_WIDTH    == IN_IW);
        assert(OUT_IW >= IN_IW); // this could be removed with proper ID remapping
        assert(OUT_DW >= IN_DW);
    end
    `endif

    // The write queue keeps track of the data and strobes that need to go onto
    // the AXI W channel.
    typedef struct packed {
        logic [ALIGN_DIFF_REQ-1:0] offset;
        logic [IN_DW-1:0]          data;
        logic [IN_DW/8-1:0]        strb;
    } write_t;

    logic   write_queue_full;
    logic   write_queue_empty;
    write_t write_queue_in, write_queue_out;

    assign write_queue_in = '{
        reqrsp_i.qaddr >> IN_ALIGN,
        reqrsp_i.qdata,
        reqrsp_i.qstrb
    };

    fifo #(
        .DEPTH        ( 1       ),
        .dtype        ( write_t )
    ) i_write_queue (
        .clk_i       ( clk_i                                               ),
        .rst_ni      ( rst_ni                                              ),
        .flush_i     ( 1'b0                                                ),
        .testmode_i  ( 1'b0                                                ),
        .full_o      ( write_queue_full                                    ),
        .empty_o     ( write_queue_empty                                   ),
        .threshold_o (                                                     ),
        .data_i      ( write_queue_in                                      ),
        .push_i      ( reqrsp_i.qvalid & reqrsp_i.qready & reqrsp_i.qwrite ),
        .data_o      ( write_queue_out                                     ),
        .pop_i       ( axi_o.w_valid & axi_o.w_ready & axi_o.w_last        )
    );

    // The read queue keeps track of the alignment of read data.
    typedef struct packed {
        logic [ALIGN_DIFF_RSP-1:0] offset;
    } read_t;

    logic  read_queue_full;
    logic  read_queue_empty;
    read_t read_queue_in, read_queue_out;

    assign read_queue_in = '{reqrsp_i.qaddr >> IN_ALIGN};

    fifo #(
        .DEPTH ( NUM_PENDING ),
        .dtype ( read_t      )
    ) i_read_queue (
        .clk_i       ( clk_i                                                ),
        .rst_ni      ( rst_ni                                               ),
        .flush_i     ( 1'b0                                                 ),
        .testmode_i  ( 1'b0                                                 ),
        .full_o      ( read_queue_full                                      ),
        .empty_o     ( read_queue_empty                                     ),
        .threshold_o (                                                      ),
        .data_i      ( read_queue_in                                        ),
        .push_i      ( reqrsp_i.qvalid & reqrsp_i.qready & ~reqrsp_i.qwrite ),
        .data_o      ( read_queue_out                                       ),
        .pop_i       ( axi_o.r_valid & axi_o.r_ready & axi_o.r_last         )
    );

    // Generate the appropriate AW and AR requests from the incoming request.
    always_comb begin : p_aw_ar
        axi_o.aw_id     = reqrsp_i.qid;
        axi_o.aw_addr   = reqrsp_i.qaddr >> OUT_ALIGN << OUT_ALIGN;
        axi_o.aw_len    = 2**ALIGN_DIFF_REQ - 1;
        axi_o.aw_size   = IN_ALIGN < OUT_ALIGN ? IN_ALIGN : OUT_ALIGN;
        axi_o.aw_burst  = axi_pkg::BURST_INCR;
        axi_o.aw_lock   = '0;
        axi_o.aw_cache  = '0;
        axi_o.aw_prot   = '0;
        axi_o.aw_qos    = '0;
        axi_o.aw_region = '0;
        axi_o.aw_user   = '0;
        axi_o.aw_valid  = '0;
        axi_o.aw_atop   = '0;

        axi_o.ar_id     = reqrsp_i.qid;
        axi_o.ar_addr   = reqrsp_i.qaddr >> OUT_ALIGN << OUT_ALIGN;
        axi_o.ar_len    = 2**ALIGN_DIFF_REQ - 1;
        axi_o.ar_size   = IN_ALIGN < OUT_ALIGN ? IN_ALIGN : OUT_ALIGN;
        axi_o.ar_burst  = axi_pkg::BURST_INCR;
        axi_o.ar_lock   = '0;
        axi_o.ar_cache  = '0;
        axi_o.ar_prot   = '0;
        axi_o.ar_qos    = '0;
        axi_o.ar_region = '0;
        axi_o.ar_user   = '0;
        axi_o.ar_valid  = '0;
        reqrsp_i.qready = 0;

        if (reqrsp_i.qvalid) begin
            if (reqrsp_i.qwrite) begin
                axi_o.aw_valid = ~write_queue_full;
                reqrsp_i.qready = axi_o.aw_ready & ~write_queue_full;
            end else begin
                axi_o.ar_valid = ~read_queue_full;
                reqrsp_i.qready = axi_o.ar_ready & ~read_queue_full;
            end
        end
    end

    // Generate the W transactions.
    logic [ALIGN_DIFF_REQ-1:0] w_count, w_count_q;

    if (IN_DW > OUT_DW) begin
        always_ff @(posedge clk_i, negedge rst_ni) begin
            if (!rst_ni)
                w_count_q <= 0;
            else if (axi_o.w_valid && axi_o.w_ready && IN_DW > OUT_DW)
                w_count_q <= w_count_q + 1;
        end
        assign w_count = w_count_q;
    end else begin
        assign w_count = 0;
    end

    always_comb begin : p_w
        if (IN_DW > OUT_DW) begin
            axi_o.w_data = write_queue_out.data >> (w_count * OUT_DW);
            axi_o.w_strb = write_queue_out.strb >> (w_count * OUT_DW);
        end else begin
            for (int i = 0; i < OUT_DW/IN_DW; i++) begin
                axi_o.w_data[i*IN_DW   +: IN_DW  ] = write_queue_out.data;
                // axi_o.w_strb[i*IN_DW/8 +: IN_DW/8] = write_queue_out.strb;
            end
            // axi_o.w_strb &= ~('1 << IN_DW/8) << (write_queue_out.offset * IN_DW/8);
            axi_o.w_strb = write_queue_out.strb;
        end
        axi_o.w_last  = w_count == 2**ALIGN_DIFF_REQ - 1;
        axi_o.w_user  = 0;
        axi_o.w_valid = ~write_queue_empty;
    end

    // The arbitration flag is used as a tie breaker when both a B and R beat
    // are available.
    logic arb_q, arb_dn;

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (!rst_ni)
            arb_q <= 0;
        else
            arb_q <= ~arb_dn;
    end


    // Receive the B and R responses.
    always_comb begin : p_b_r
        axi_o.b_ready = 0;
        axi_o.r_ready = 0;
        reqrsp_i.pdata  = 0;
        reqrsp_i.perror = 0;
        reqrsp_i.pid    = 0;
        reqrsp_i.pvalid = 0;

        // Arbitrate between the incoming requests.
        if (axi_o.b_valid && axi_o.r_valid)
            arb_dn = arb_q;
        else if (axi_o.b_valid)
            arb_dn = 0;
        else if (axi_o.r_valid)
            arb_dn = 1;
        else
            arb_dn = ~arb_q;

        // Handle write responses.
        if (axi_o.b_valid && arb_dn == 0) begin
            reqrsp_i.perror = axi_o.b_resp != axi_pkg::RESP_OKAY;
            reqrsp_i.pid    = axi_o.b_id;
            reqrsp_i.pvalid = 1;
            axi_o.b_ready   = reqrsp_i.pready;
        end

        // Handle read responses.
        if (axi_o.r_valid && arb_dn == 1 && !read_queue_empty) begin
            reqrsp_i.pdata  = axi_o.r_data; // >> (read_queue_out.offset * IN_DW);
            reqrsp_i.perror = axi_o.r_resp != axi_pkg::RESP_OKAY;
            reqrsp_i.pid    = axi_o.r_id;
            reqrsp_i.pvalid = 1;
            axi_o.r_ready   = reqrsp_i.pready;
        end
    end

endmodule
