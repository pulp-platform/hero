// Copyright (c) 2017-2019 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

module snitch_icache #(
    /// Number of request (fetch) ports
    parameter int NR_FETCH_PORTS = -1,
    /// L0 Cache Line Count
    parameter int L0_LINE_COUNT = -1,
    /// Cache Line Width
    parameter int LINE_WIDTH = -1,
    /// The number of cache lines per set. Power of two; >= 2.
    parameter int LINE_COUNT = -1,
    /// The set associativity of the cache. Power of two; >= 1.
    parameter int SET_COUNT = 1,
    /// Fetch interface address width. Power of two; >= 1.
    parameter int FETCH_AW = -1,
    /// Fetch interface data width. Power of two; >= 8.
    parameter int FETCH_DW = -1,
    /// Fill interface address width. Power of two; >= 1.
    parameter int FILL_AW = -1,
    /// Fill interface data width. Power of two; >= 8.
    parameter int FILL_DW = -1,
    /// Add an optional private cache for each port. If enabled, the early
    /// cache will be added if the fetch data width is smaller than the cache
    /// line.
    parameter bit EARLY_ENABLED = 1,
    /// This reduces area impact at the cost of
    /// increased hassle of having latches in
    /// the design.
    /// i_snitch_icache/gen_prefetcher*i_snitch_icache_l0/data*/Q
    parameter bit EARLY_LATCH = 0,
    /// Make the early cache serve responses combinatorially if possible. Set
    /// this to 0 to cut combinatorial paths into the fetch interface.
    parameter bit EARLY_FALLTHROUGH = 0
) (
    input  logic clk_i,
    input  logic rst_ni,

    input  logic flush_valid_i,
    output logic flush_ready_o,

    input  logic [NR_FETCH_PORTS-1:0][FETCH_AW-1:0] inst_addr_i,
    output logic [NR_FETCH_PORTS-1:0][FETCH_DW-1:0] inst_data_o,
    input  logic [NR_FETCH_PORTS-1:0]               inst_cacheable_i,
    input  logic [NR_FETCH_PORTS-1:0]               inst_valid_i,
    output logic [NR_FETCH_PORTS-1:0]               inst_ready_o,
    output logic [NR_FETCH_PORTS-1:0]               inst_error_o,
    // AXI-like read-only interface
    output logic [FILL_AW-1:0]   refill_qaddr_o,
    output logic [7:0]           refill_qlen_o,
    output logic                 refill_qvalid_o,
    input  logic                 refill_qready_i,

    input  logic [FILL_DW-1:0]   refill_pdata_i,
    input  logic                 refill_perror_i,
    input  logic                 refill_pvalid_i,
    input  logic                 refill_plast_i,
    output logic                 refill_pready_o
);

    // Bundle the parameters up into a proper configuration struct that we can
    // pass to submodules.
    localparam snitch_icache_pkg::config_t CFG = '{
        NR_FETCH_PORTS:    NR_FETCH_PORTS,
        LINE_WIDTH:        LINE_WIDTH,
        LINE_COUNT:        LINE_COUNT,
        L0_LINE_COUNT:     L0_LINE_COUNT,
        SET_COUNT:         SET_COUNT,
        PENDING_COUNT:     2,
        FETCH_AW:          FETCH_AW,
        FETCH_DW:          FETCH_DW,
        FILL_AW:           FILL_AW,
        FILL_DW:           FILL_DW,
        EARLY_ENABLED:     EARLY_ENABLED,
        EARLY_LATCH:       EARLY_LATCH,
        EARLY_FALLTHROUGH: EARLY_FALLTHROUGH,

        FETCH_ALIGN: $clog2(FETCH_DW/8),
        FILL_ALIGN:  $clog2(FILL_DW/8),
        LINE_ALIGN:  $clog2(LINE_WIDTH/8),
        COUNT_ALIGN: $clog2(LINE_COUNT),
        SET_ALIGN:   $clog2(SET_COUNT),
        TAG_WIDTH:   FETCH_AW - $clog2(LINE_WIDTH/8) - $clog2(LINE_COUNT) + 1,
        L0_TAG_WIDTH: FETCH_AW - $clog2(LINE_WIDTH/8),
        ID_WIDTH_REQ: $clog2(NR_FETCH_PORTS) + 1,
        ID_WIDTH_RESP: 2*NR_FETCH_PORTS,
        PENDING_IW:  $clog2(2)
    };

    // pragma translate_off
    `ifndef VERILATOR
    // Check invariants.
    initial begin
        assert(L0_LINE_COUNT > 0);
        assert(LINE_WIDTH > 0);
        assert(LINE_COUNT > 1);
        assert(SET_COUNT >= 2) else $warning("Only >= 2 sets are supported");
        assert(FETCH_AW > 0);
        assert(FETCH_DW > 0);
        assert(FILL_AW > 0);
        assert(FILL_DW > 0);
        assert(2**$clog2(LINE_WIDTH) == LINE_WIDTH);
        assert(2**$clog2(LINE_COUNT) == LINE_COUNT);
        assert(2**$clog2(SET_COUNT) == SET_COUNT);
        assert(2**$clog2(FETCH_AW) == FETCH_AW);
        assert(2**$clog2(FETCH_DW) == FETCH_DW);
        assert(2**$clog2(FILL_AW) == FILL_AW);
        assert(2**$clog2(FILL_DW) == FILL_DW);
    end
    `endif
    // pragma translate_on

    // Instantiate the optional early cache, or bypass it.
    logic [NR_FETCH_PORTS-1:0][FETCH_AW-1:0]   early_addr;
    logic [NR_FETCH_PORTS-1:0][LINE_WIDTH-1:0] early_data;
    logic [NR_FETCH_PORTS-1:0]                 early_valid;
    logic [NR_FETCH_PORTS-1:0]                 early_ready;
    logic [NR_FETCH_PORTS-1:0]                 early_error;

    // The prefetch module is responsible for taking the 1-channel valid/ready
    // transaction from the early cache and translate it into a 2-channel
    // transaction. Once the actual incoming request has been accepted on the
    // `req` channel, the prefetcher issues another low-priority request for the
    // next cache line.
    typedef struct packed {
        logic [CFG.FETCH_AW-1:0]     addr;
        logic [CFG.ID_WIDTH_REQ-1:0] id;
    } prefetch_req_t;

    typedef struct packed {
        logic [CFG.LINE_WIDTH-1:0]    data;
        logic                         error;
        logic [CFG.ID_WIDTH_RESP-1:0] id;
    } prefetch_resp_t;

    prefetch_req_t [NR_FETCH_PORTS-1:0] prefetch_req       ;
    logic          [NR_FETCH_PORTS-1:0] prefetch_req_valid ;
    logic          [NR_FETCH_PORTS-1:0] prefetch_req_ready ;

    prefetch_req_t prefetch_lookup_req       ;
    logic          prefetch_lookup_req_valid ;
    logic          prefetch_lookup_req_ready ;

    prefetch_resp_t [NR_FETCH_PORTS-1:0]  prefetch_rsp       ;
    logic           [NR_FETCH_PORTS-1:0]  prefetch_rsp_valid ;
    logic           [NR_FETCH_PORTS-1:0]  prefetch_rsp_ready ;

    prefetch_resp_t prefetch_lookup_rsp       ;
    logic           prefetch_lookup_rsp_valid ;
    logic           prefetch_lookup_rsp_ready ;

    typedef struct packed {
        logic [CFG.FETCH_AW-1:0]   addr;
        logic [CFG.PENDING_IW-1:0] id;
        logic                      bypass;
    } miss_refill_req_t;
    miss_refill_req_t handler_req, bypass_req, refill_req;
    logic handler_req_valid, bypass_req_valid, refill_req_valid;
    logic handler_req_ready, bypass_req_ready, refill_req_ready;

    typedef struct packed {
        logic [CFG.LINE_WIDTH-1:0] data;
        logic                      error;
        logic [CFG.PENDING_IW-1:0] id;
        logic                      bypass;
    } miss_refill_rsp_t;
    miss_refill_rsp_t handler_rsp, bypass_rsp, refill_rsp;
    logic handler_rsp_valid, bypass_rsp_valid, refill_rsp_valid;
    logic handler_rsp_ready, bypass_rsp_ready, refill_rsp_ready;

    logic [NR_FETCH_PORTS-1:0][FETCH_DW-1:0] bypass_data;
    logic [NR_FETCH_PORTS-1:0]               bypass_error;
    logic [NR_FETCH_PORTS-1:0]               bypass_valid;
    logic [NR_FETCH_PORTS-1:0]               bypass_ready;
    logic [NR_FETCH_PORTS-1:0][FETCH_AW-1:0] bypass_addr;

    // logic [NR_FETCH_PORTS-1:0]
    logic [NR_FETCH_PORTS-1:0] in_cache_valid, in_bypass_valid;
    logic [NR_FETCH_PORTS-1:0] in_cache_ready, in_bypass_ready;
    logic [NR_FETCH_PORTS-1:0] [FETCH_DW-1:0] in_cache_data, in_bypass_data;
    logic [NR_FETCH_PORTS-1:0] in_cache_error, in_bypass_error;
    for (genvar i = 0; i < NR_FETCH_PORTS; i++) begin : gen_prefetcher

        assign in_cache_valid[i] = inst_cacheable_i[i] & inst_valid_i[i];
        assign in_bypass_valid[i] = ~inst_cacheable_i[i] & inst_valid_i[i];
        assign inst_ready_o[i] = (inst_cacheable_i[i] & in_cache_ready [i]) | (~inst_cacheable_i[i] & in_bypass_ready [i]);
        // multiplex results
        assign {inst_error_o[i], inst_data_o[i]} = ({($bits(in_cache_data[i])+1){inst_cacheable_i[i]}} & {in_cache_error [i], in_cache_data[i]})
                                                | (~{($bits(in_cache_data[i])+1){inst_cacheable_i[i]}} & {in_bypass_error[i], in_bypass_data[i]});

        snitch_icache_l0 #(
            .CFG         ( CFG ),
            .PREFETCH_ID ( i   )
        ) i_snitch_icache_l0 (
            .clk_i,
            .rst_ni,
            .flush_valid_i,

            .in_addr_i       ( inst_addr_i    [i]     ),
            .in_data_o       ( in_cache_data  [i]     ),
            .in_error_o      ( in_cache_error [i]     ),
            .in_valid_i      ( in_cache_valid [i]     ),
            .in_ready_o      ( in_cache_ready [i]     ),

            .out_req_addr_o  ( prefetch_req[i].addr   ),
            .out_req_id_o    ( prefetch_req[i].id     ),
            .out_req_valid_o ( prefetch_req_valid [i] ),
            .out_req_ready_i ( prefetch_req_ready [i] ),

            .out_rsp_data_i  ( prefetch_rsp[i].data   ),
            .out_rsp_error_i ( prefetch_rsp[i].error  ),
            .out_rsp_id_i    ( prefetch_rsp[i].id     ),
            .out_rsp_valid_i ( prefetch_rsp_valid [i] ),
            .out_rsp_ready_o ( prefetch_rsp_ready [i] )
        );
    end

    l0_to_bypass #(
        .CFG         ( CFG )
    ) i_l0_to_bypass (
        .clk_i,
        .rst_ni,

        .in_valid_i ( in_bypass_valid ),
        .in_ready_o ( in_bypass_ready ),
        .in_addr_i  ( inst_addr_i     ),
        .in_data_o  ( in_bypass_data  ),
        .in_error_o ( in_bypass_error ),

        .refill_req_addr_o   ( bypass_req.addr   ),
        .refill_req_bypass_o ( bypass_req.bypass ),
        .refill_req_valid_o  ( bypass_req_valid  ),
        .refill_req_ready_i  ( bypass_req_ready  ),

        .refill_rsp_data_i   ( bypass_rsp.data  ),
        .refill_rsp_error_i  ( bypass_rsp.error ),
        .refill_rsp_valid_i  ( bypass_rsp_valid ),
        .refill_rsp_ready_o  ( bypass_rsp_ready )
    );

    assign bypass_req.id = '0;

    /// Arbitrate cache port
    // 1. Request Side
    stream_arbiter #(
        .DATA_T ( prefetch_req_t ),
        .N_INP  ( NR_FETCH_PORTS )
    ) i_stream_arbiter (
        .clk_i,
        .rst_ni,
        .inp_data_i  ( prefetch_req              ),
        .inp_valid_i ( prefetch_req_valid        ),
        .inp_ready_o ( prefetch_req_ready        ),
        .oup_data_o  ( prefetch_lookup_req       ),
        .oup_valid_o ( prefetch_lookup_req_valid ),
        .oup_ready_i ( prefetch_lookup_req_ready )
    );

    // 2. Response Side
    // This breaks if the pre-fetcher would not alway be ready
    // which is the case for the moment
    for (genvar i = 0; i < NR_FETCH_PORTS; i++) begin : gen_resp
        assign prefetch_rsp[i] = prefetch_lookup_rsp;
        // check if one of the ID bits is set
        assign prefetch_rsp_valid[i] = ((|((prefetch_rsp[i].id >> 2*i) & 2'b11)) & prefetch_lookup_rsp_valid);
    end
    assign prefetch_lookup_rsp_ready = |prefetch_rsp_ready;

    /// Tag lookup

    // The lookup module contains the actual cache RAMs and performs lookups.
    logic [CFG.FETCH_AW-1:0]     lookup_addr  ;
    logic [CFG.ID_WIDTH_REQ-1:0] lookup_id    ;
    logic [CFG.SET_ALIGN-1:0]    lookup_set   ;
    logic                        lookup_hit   ;
    logic [CFG.LINE_WIDTH-1:0]   lookup_data  ;
    logic                        lookup_error ;
    logic                        lookup_valid ;
    logic                        lookup_ready ;

    logic [CFG.COUNT_ALIGN-1:0]  write_addr  ;
    logic [CFG.SET_ALIGN-1:0]    write_set   ;
    logic [CFG.LINE_WIDTH-1:0]   write_data  ;
    logic [CFG.TAG_WIDTH-1:0]    write_tag   ;
    logic                        write_error ;
    logic                        write_valid ;
    logic                        write_ready ;

    snitch_icache_lookup #(CFG) i_lookup (
        .clk_i,
        .rst_ni,

        .flush_valid_i,
        .flush_ready_o,

        .in_addr_i     ( prefetch_lookup_req.addr  ),
        .in_id_i       ( prefetch_lookup_req.id    ),
        .in_valid_i    ( prefetch_lookup_req_valid ),
        .in_ready_o    ( prefetch_lookup_req_ready ),

        .out_addr_o    ( lookup_addr        ),
        .out_id_o      ( lookup_id          ),
        .out_set_o     ( lookup_set         ),
        .out_hit_o     ( lookup_hit         ),
        .out_data_o    ( lookup_data        ),
        .out_error_o   ( lookup_error       ),
        .out_valid_o   ( lookup_valid       ),
        .out_ready_i   ( lookup_ready       ),

        .write_addr_i  ( write_addr         ),
        .write_set_i   ( write_set          ),
        .write_data_i  ( write_data         ),
        .write_tag_i   ( write_tag          ),
        .write_error_i ( write_error        ),
        .write_valid_i ( write_valid        ),
        .write_ready_o ( write_ready        )
    );

    // The miss handler module deals with the result of the lookup. It also
    // keeps track of the pending refills and ensures that no redundant memory
    // requests are made. Upon refill completion, it sends a new tag/data item
    // to the lookup module and the received data to the prefetch module.
    snitch_icache_handler #(CFG) i_handler (
        .clk_i,
        .rst_ni,

        .in_req_addr_i   ( lookup_addr        ),
        .in_req_id_i     ( lookup_id          ),
        .in_req_set_i    ( lookup_set         ),
        .in_req_hit_i    ( lookup_hit         ),
        .in_req_data_i   ( lookup_data        ),
        .in_req_error_i  ( lookup_error       ),
        .in_req_valid_i  ( lookup_valid       ),
        .in_req_ready_o  ( lookup_ready       ),

        .in_rsp_data_o   ( prefetch_lookup_rsp.data  ),
        .in_rsp_error_o  ( prefetch_lookup_rsp.error ),
        .in_rsp_id_o     ( prefetch_lookup_rsp.id    ),
        .in_rsp_valid_o  ( prefetch_lookup_rsp_valid ),
        .in_rsp_ready_i  ( prefetch_lookup_rsp_ready ),

        .write_addr_o    ( write_addr         ),
        .write_set_o     ( write_set          ),
        .write_data_o    ( write_data         ),
        .write_tag_o     ( write_tag          ),
        .write_error_o   ( write_error        ),
        .write_valid_o   ( write_valid        ),
        .write_ready_i   ( write_ready        ),

        .out_req_addr_o  ( handler_req.addr    ),
        .out_req_id_o    ( handler_req.id      ),
        .out_req_valid_o ( handler_req_valid   ),
        .out_req_ready_i ( handler_req_ready   ),

        .out_rsp_data_i  ( handler_rsp.data    ),
        .out_rsp_error_i ( handler_rsp.error   ),
        .out_rsp_id_i    ( handler_rsp.id      ),
        .out_rsp_valid_i ( handler_rsp_valid   ),
        .out_rsp_ready_o ( handler_rsp_ready   )
    );
    assign handler_req.bypass = 1'b0;
    // Arbitrate between bypass and cache-refills
    stream_arbiter #(
        .DATA_T ( miss_refill_req_t ),
        .N_INP  ( 2                 )
    ) i_stream_arbiter_miss_refill (
        .clk_i,
        .rst_ni,
        .inp_data_i  ( {bypass_req, handler_req}             ),
        .inp_valid_i ( {bypass_req_valid, handler_req_valid} ),
        .inp_ready_o ( {bypass_req_ready, handler_req_ready} ),
        .oup_data_o  ( refill_req                            ),
        .oup_valid_o ( refill_req_valid                      ),
        .oup_ready_i ( refill_req_ready                      )
    );
    // Response path muxing
    stream_demux #(
        .N_OUP  ( 2                 )
    ) i_stream_demux_miss_refill (
        .inp_valid_i ( refill_rsp_valid  ),
        .inp_ready_o ( refill_rsp_ready  ),

        .oup_sel_i   ( refill_rsp.bypass ),

        .oup_valid_o ( {{bypass_rsp_valid, handler_rsp_valid}} ),
        .oup_ready_i ( {{bypass_rsp_ready, handler_rsp_ready}} )
    );

    assign handler_rsp = refill_rsp;
    assign bypass_rsp = refill_rsp;

    // AXI-like read-only interface
    typedef struct packed {
        logic [FILL_AW-1:0] addr;
        logic [7:0]         len;
    } extern_req_t;

    typedef struct packed {
        logic [FILL_DW-1:0] data;
        logic               error;
        logic               last;
    } extern_rsp_t;

    extern_req_t          extern_req, extern_req_q;
    logic                 extern_qvalid;
    logic                 extern_qready;

    extern_rsp_t          extern_rsp, extern_rsp_q;
    logic                 extern_pvalid_q;
    logic                 extern_pready_q;

    // Instantiate the cache refill module which emits AXI transactions.
    snitch_icache_refill #(CFG) i_refill (
        .clk_i,
        .rst_ni,

        .in_req_addr_i   ( refill_req.addr    ),
        .in_req_id_i     ( refill_req.id      ),
        .in_req_bypass_i ( refill_req.bypass  ),
        .in_req_valid_i  ( refill_req_valid   ),
        .in_req_ready_o  ( refill_req_ready   ),

        .in_rsp_data_o   ( refill_rsp.data    ),
        .in_rsp_error_o  ( refill_rsp.error   ),
        .in_rsp_id_o     ( refill_rsp.id      ),
        .in_rsp_bypass_o ( refill_rsp.bypass  ),
        .in_rsp_valid_o  ( refill_rsp_valid   ),
        .in_rsp_ready_i  ( refill_rsp_ready   ),

        .refill_qaddr_o  ( extern_req.addr    ),
        .refill_qlen_o   ( extern_req.len     ),
        .refill_qvalid_o ( extern_qvalid      ),
        .refill_qready_i ( extern_qready      ),
        .refill_pdata_i  ( extern_rsp_q.data  ),
        .refill_perror_i ( extern_rsp_q.error ),
        .refill_plast_i  ( extern_rsp_q.last  ),
        .refill_pvalid_i ( extern_pvalid_q    ),
        .refill_pready_o ( extern_pready_q    )
    );

    // Insert Slices.
    spill_register #(.T(extern_req_t)) i_spill_register_req (
        .clk_i,
        .rst_ni,
        .valid_i ( extern_qvalid   ),
        .ready_o ( extern_qready   ),
        .data_i  ( extern_req      ),
        // Q Output
        .valid_o ( refill_qvalid_o ),
        .ready_i ( refill_qready_i ),
        .data_o  ( extern_req_q    )
    );

    assign refill_qaddr_o = extern_req_q.addr;
    assign refill_qlen_o = extern_req_q.len;

    spill_register #(.T(extern_rsp_t)) i_spill_register_resp (
        .clk_i,
        .rst_ni,
        .valid_i ( refill_pvalid_i ),
        .ready_o ( refill_pready_o ),
        .data_i  ( extern_rsp      ),
        // Q Output
        .valid_o ( extern_pvalid_q ),
        .ready_i ( extern_pready_q ),
        .data_o  ( extern_rsp_q    )
    );

    assign extern_rsp.data = refill_pdata_i;
    assign extern_rsp.error = refill_perror_i;
    assign extern_rsp.last = refill_plast_i;
endmodule

// Translate register interface to refill requests.
// Used for bypassable accesses.
module l0_to_bypass #(
    parameter snitch_icache_pkg::config_t CFG = '0
) (
    input  logic                clk_i,
    input  logic                rst_ni,

    input  logic [CFG.NR_FETCH_PORTS-1:0]                   in_valid_i,
    output logic [CFG.NR_FETCH_PORTS-1:0]                   in_ready_o,
    input  logic [CFG.NR_FETCH_PORTS-1:0][CFG.FETCH_AW-1:0] in_addr_i,
    output logic [CFG.NR_FETCH_PORTS-1:0][CFG.FETCH_DW-1:0] in_data_o,
    output logic [CFG.NR_FETCH_PORTS-1:0]                   in_error_o,

    output logic [CFG.FETCH_AW-1:0] refill_req_addr_o,
    output logic                refill_req_bypass_o,
    output logic                refill_req_valid_o,
    input  logic                refill_req_ready_i,

    input  logic [CFG.LINE_WIDTH-1:0] refill_rsp_data_i,
    input  logic                  refill_rsp_error_i,
    input  logic                  refill_rsp_valid_i,
    output logic                  refill_rsp_ready_o
);

    assign refill_req_bypass_o = 1'b1;

    logic [CFG.NR_FETCH_PORTS-1:0] in_valid;
    logic [CFG.NR_FETCH_PORTS-1:0] in_ready;

    enum logic [1:0] {
        Idle, RequestData, WaitResponse, PresentResponse
    } state_d [CFG.NR_FETCH_PORTS-1:0], state_q [CFG.NR_FETCH_PORTS-1:0];

    // Mask address so that it is aligned to the cache-line width.
    logic [CFG.NR_FETCH_PORTS-1:0][CFG.FETCH_AW-1:0] in_addr_masked;
    for (genvar i = 0; i < CFG.NR_FETCH_PORTS; i++) begin
        assign in_addr_masked[i] = in_addr_i[i] >> CFG.LINE_ALIGN << CFG.LINE_ALIGN;
    end
    stream_arbiter #(
        .DATA_T ( logic [CFG.FETCH_AW-1:0] ),
        .N_INP  ( CFG.NR_FETCH_PORTS )
    ) i_stream_arbiter (
        .clk_i,
        .rst_ni,
        .inp_data_i  ( in_addr_masked     ),
        .inp_valid_i ( in_valid           ),
        .inp_ready_o ( in_ready           ),
        .oup_data_o  ( refill_req_addr_o  ),
        .oup_valid_o ( refill_req_valid_o ),
        .oup_ready_i ( refill_req_ready_i )
    );

    localparam int unsigned NR_FETCH_PORTS_BIN = CFG.NR_FETCH_PORTS == 1 ? 1 : $clog2(CFG.NR_FETCH_PORTS);

    logic [CFG.NR_FETCH_PORTS-1:0] rsp_fifo_mux;
    logic [NR_FETCH_PORTS_BIN-1:0] onehot_mux;
    logic [CFG.NR_FETCH_PORTS-1:0] rsp_fifo_pop;
    logic rsp_fifo_full;

    logic [CFG.NR_FETCH_PORTS-1:0] rsp_valid;
    logic [CFG.NR_FETCH_PORTS-1:0] rsp_ready;

    fifo_v3 #(
        .DATA_WIDTH ( CFG.NR_FETCH_PORTS ),
        .DEPTH      ( 4              )
    ) rsp_fifo (
        .clk_i,
        .rst_ni,
        .flush_i    ( 1'b0                  ),
        .testmode_i ( 1'b0                  ),
        .full_o     ( rsp_fifo_full         ),
        .empty_o    (                       ),
        .usage_o    (                       ),
        .data_i     ( {in_valid & in_ready} ),
        .push_i     ( |{in_valid & in_ready}),
        .data_o     ( rsp_fifo_mux          ),
        .pop_i      ( |rsp_fifo_pop         )
    );


    onehot_to_bin #(
        .ONEHOT_WIDTH (CFG.NR_FETCH_PORTS)
    ) i_onehot_to_bin (
        .onehot (rsp_fifo_mux),
        .bin (onehot_mux)
    );

    assign rsp_ready = '1;

    stream_demux #(
        .N_OUP  ( CFG.NR_FETCH_PORTS     )
    ) i_stream_mux_miss_refill (
        .inp_valid_i ( refill_rsp_valid_i ),
        .inp_ready_o ( refill_rsp_ready_o ),
        .oup_sel_i   ( onehot_mux ),
        .oup_valid_o ( rsp_valid ),
        .oup_ready_i ( rsp_ready )
    );

    for (genvar i = 0; i < CFG.NR_FETCH_PORTS; i++) begin : gen_bypass_request
        always_comb begin
            state_d[i] = state_q[i];
            in_ready_o[i] = 1'b0;
            rsp_fifo_pop[i] = 1'b0;
            in_valid[i] = 1'b0;
            unique case (state_q[i])
                // latch data when idle
                Idle: if (in_valid_i[i]) state_d[i] = RequestData;
                RequestData: begin
                    // check that there is still space for the response to be accepted.
                    if (!rsp_fifo_full) begin
                        in_valid[i] = 1'b1;
                        if (in_ready[i]) state_d[i] = WaitResponse;
                    end
                end
                WaitResponse: begin
                    if (rsp_valid[i]) begin
                        rsp_fifo_pop[i] = 1'b1;
                        state_d[i] = PresentResponse;
                    end
                end
                // The response will be served from the register and is valid for one cycle.
                PresentResponse: begin
                    state_d[i] = Idle;
                    in_ready_o[i] = 1'b1;
                end
                default:;
            endcase
        end
        logic [CFG.FILL_DW-1:0] fill_rsp_data;
        assign fill_rsp_data = refill_rsp_data_i >> (in_addr_i[i][CFG.LINE_ALIGN-1:CFG.FETCH_ALIGN] * CFG.FETCH_DW);
        `FFLNR({in_data_o[i], in_error_o[i]}, {fill_rsp_data[CFG.FETCH_DW-1:0], refill_rsp_error_i}, rsp_valid[i], clk_i)
    end

    `FF(state_q, state_d, '{default: Idle})

endmodule
