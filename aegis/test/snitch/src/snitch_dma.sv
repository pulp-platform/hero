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

// A simple descriptor based DMA originally developed for the Baikonur chip.
// To initiate a DMA transfer a pointer to a memory location containing the descriptor
// should be pushed to the memory mapped configuration interface.
// The DMA will go and fetch the descriptor from that particular memory location.
// The configuration interface has FIFO semantic, e.g. the programmer can push multiple
// addresses to descriptors without blocking.
//
// Once the DMA has read the descriptor from memory it start the memory transfer.
// Upon completion it clears the memory location, an event which can be observed by
// software by reading from the descriptor memory location.
//
// Limitations: Only aligned, 1D transfers are supported at the moment. The
// descriptor already provisions for more complex transfers though.
module snitch_dma (
    input  logic clk_i,
    input  logic rst_ni,

    output snitch_axi_pkg::req_t req_o,
    input  snitch_axi_pkg::resp_t rsp_i,

    // TODO(zarubaf): On-board to configuration interface.
    input  kosmo_pkg::apb_req_t cfg_req_i,
    output kosmo_pkg::apb_rsp_t cfg_rsp_o
);

    //////////////////////////////////
    //   DESCRIPTOR ADDRESS FIFOS   //
    //////////////////////////////////

    logic [1:0] desc_fifo_full;
    logic [1:0] desc_fifo_empty;
    logic [1:0] desc_fifo_push;
    logic [1:0] desc_fifo_pop;
    logic [1:0][31:0] desc_fifo_data_in;
    logic [1:0][31:0] desc_fifo_data_out;

    // APB into FIFOs
    always_comb begin
        cfg_rsp_o.ready = 1;
        for (int i = 0; i < 2; i++) begin
            desc_fifo_push[i] = 0;
            desc_fifo_data_in[i] = cfg_req_i.wdata;
            cfg_rsp_o.ready &= ~desc_fifo_full[i];
            if (~desc_fifo_full[i] && cfg_req_i.sel && cfg_req_i.enable && cfg_req_i.write && cfg_req_i.addr == i*4) begin
                desc_fifo_push[i] = 1;
            end
        end
    end

    // FIFOs
    // Configuration FIFO, this determines the maximum outstanding transactions
    // before the configuration interface begins to block.
    for (genvar i = 0; i < 2; i++) begin
        fifo_v3 #(
            .DATA_WIDTH ( 32 ),
            .DEPTH      ( 8  )
        ) i_fifo (
            .clk_i,
            .rst_ni,
            .flush_i    ( 1'b0                  ),
            .testmode_i ( 1'b0                  ),
            .full_o     ( desc_fifo_full[i]     ),
            .empty_o    ( desc_fifo_empty[i]    ),
            .usage_o    (                       ),
            .data_i     ( desc_fifo_data_in[i]  ),
            .push_i     ( desc_fifo_push[i]     ),
            .data_o     ( desc_fifo_data_out[i] ),
            .pop_i      ( desc_fifo_pop[i]      )
        );
    end

    // FIFOs into control
    logic [63:0] desc_addr;
    logic desc_addr_valid;
    logic desc_addr_ready;

    always_comb begin
        desc_addr = desc_fifo_data_out;
        desc_addr_valid = &(~desc_fifo_empty);
        desc_fifo_pop = desc_addr_valid & desc_addr_ready ? '1 : '0;
    end


    /////////////////////
    //   CONTROL FSM   //
    /////////////////////
    // The control FSM mainly distinguishes between three different states:
    // 1. Setup - Go and fetch the descriptor from a memory location.
    // 2. Run - Do the actual memcpy
    // 3. Finish - Clear the descriptor to signal readiness to the software.
    // Communication with the `mover FSM` is done through valid-then-ready handshakes.

    // States
    enum logic [1:0] {
        Idle,
        Setup,
        Run,
        Finish
    } state_d, state_q;

    `FF(state_q, state_d, Idle)

    // Descriptor and address calculation.
    struct packed {
        logic [63:0] src_addr;
        logic [63:0] dst_addr;
        logic [31:0] length;
        // logic [1:0][31:0] stride;
        // logic [1:0][31:0] bound;
        logic [31:0] ctrlstat;
    } desc_d, desc_q;

    `FF(desc_q, desc_d, '0)

    logic [12:0] src_max_len, dst_max_len, bus_max_len;

    // Transfer chunks to mover.
    typedef enum logic [1:0] {
        ChunkNormal,
        ChunkDescRead,
        ChunkDescClear
    } chunk_mode_t;

    typedef struct packed {
        chunk_mode_t mode;
        logic [63:0] src_addr;
        logic [63:0] dst_addr;
        logic [7:0] len;
    } chunk_t;

    chunk_t chunk_next;
    logic chunk_next_valid;
    logic chunk_next_ready;

    logic [63:0] desc_read_data;
    logic desc_read_valid;
    logic desc_read_last;

    // FSM
    always_comb begin
        state_d = state_q;
        desc_d = desc_q;
        chunk_next = '0;
        chunk_next_valid = 0;
        desc_addr_ready = 0;

        case (state_q)
            Idle: if (desc_addr_valid) begin
                chunk_next.mode = ChunkDescRead;
                chunk_next.src_addr = desc_addr;
                chunk_next.len = ($bits(desc_q)+63)/64-1;
                chunk_next_valid = 1;
                if (chunk_next_ready) begin
                    state_d = Setup;
                end
            end
            Setup: if (desc_read_valid) begin
                desc_d = desc_q >> 64 | desc_read_data << ($bits(desc_q)-64);
                if (desc_read_last) state_d = Run;
            end
            Run: begin
                automatic logic [11:0] min_len;
                chunk_next.mode = ChunkNormal;
                chunk_next.src_addr = desc_q.src_addr;
                chunk_next.dst_addr = desc_q.dst_addr;

                min_len = bus_max_len;
                if (desc_q.length < min_len) min_len = desc_q.length;
                if (src_max_len < min_len) min_len = src_max_len;
                if (dst_max_len < min_len) min_len = dst_max_len;
                chunk_next.len = min_len/8-1;
                chunk_next_valid = 1;

                if (chunk_next_ready) begin
                    desc_d.src_addr += min_len;
                    desc_d.dst_addr += min_len;
                    desc_d.length -= min_len;
                    if (desc_d.length == 0) state_d = Finish;
                end
            end
            Finish: begin
                chunk_next.mode = ChunkDescClear;
                chunk_next.dst_addr = desc_addr;
                chunk_next_valid = 1;
                if (chunk_next_ready) begin
                    state_d = Idle;
                    desc_addr_ready = 1;
                end
            end
        endcase
    end

    assign src_max_len = (1 << 12) - desc_q.src_addr[11:0];
    assign dst_max_len = (1 << 12) - desc_q.dst_addr[11:0];
    assign bus_max_len = 256 * 8;


    ///////////////////
    //   MOVER FSM   //
    ///////////////////
    // The mover handles the interface with the AXI protocol.
    // It breaks the transfers into smaller chunks and adheres to the AXI
    // specification to break on 4k boundaries.

    // Chunk FIFOs
    typedef struct packed {
        logic [63:0] data;
        logic last;
    } mover_r_t;

    chunk_t mover_aw, mover_ar;
    chunk_mode_t mover_w;
    mover_r_t mover_r, mover_r_in;
    logic mover_aw_full, mover_w_full, mover_ar_full, mover_r_full;
    logic mover_aw_empty, mover_w_empty, mover_ar_empty, mover_r_empty;
    logic mover_aw_push, mover_w_push, mover_ar_push, mover_r_push;
    logic mover_aw_pop, mover_w_pop, mover_ar_pop, mover_r_pop;

    fifo_v3 #(
        .dtype ( chunk_t ),
        .DEPTH ( 2       )
    ) i_mover_aw_fifo (
        .clk_i,
        .rst_ni,
        .flush_i    ( 1'b0           ),
        .testmode_i ( 1'b0           ),
        .full_o     ( mover_aw_full  ),
        .empty_o    ( mover_aw_empty ),
        .usage_o    (                ),
        .data_i     ( chunk_next     ),
        .push_i     ( mover_aw_push  ),
        .data_o     ( mover_aw       ),
        .pop_i      ( mover_aw_pop   )
    );

    fifo_v3 #(
        .dtype ( chunk_mode_t ),
        .DEPTH ( 4            )
    ) i_mover_w_fifo (
        .clk_i,
        .rst_ni,
        .flush_i    ( 1'b0            ),
        .testmode_i ( 1'b0            ),
        .full_o     ( mover_w_full    ),
        .empty_o    ( mover_w_empty   ),
        .usage_o    (                 ),
        .data_i     ( chunk_next.mode ),
        .push_i     ( mover_w_push    ),
        .data_o     ( mover_w         ),
        .pop_i      ( mover_w_pop     )
    );

    fifo_v3 #(
        .dtype ( chunk_t ),
        .DEPTH ( 2       )
    ) i_mover_ar_fifo (
        .clk_i,
        .rst_ni,
        .flush_i    ( 1'b0           ),
        .testmode_i ( 1'b0           ),
        .full_o     ( mover_ar_full  ),
        .empty_o    ( mover_ar_empty ),
        .usage_o    (                ),
        .data_i     ( chunk_next     ),
        .push_i     ( mover_ar_push  ),
        .data_o     ( mover_ar       ),
        .pop_i      ( mover_ar_pop   )
    );

    fifo_v3 #(
        .dtype ( mover_r_t ),
        .DEPTH ( 16         )
    ) i_mover_r_fifo (
        .clk_i,
        .rst_ni,
        .flush_i    ( 1'b0          ),
        .testmode_i ( 1'b0          ),
        .full_o     ( mover_r_full  ),
        .empty_o    ( mover_r_empty ),
        .usage_o    (               ),
        .data_i     ( mover_r_in    ),
        .push_i     ( mover_r_push  ),
        .data_o     ( mover_r       ),
        .pop_i      ( mover_r_pop   )
    );

    assign mover_r_in = '{data: rsp_i.r.data, last: rsp_i.r.last};

    always_comb begin
        chunk_next_ready = ~mover_aw_full & ~mover_w_full & ~mover_ar_full;
        mover_aw_push = chunk_next_valid & chunk_next_ready & (chunk_next.mode != ChunkDescRead);
        mover_ar_push = chunk_next_valid & chunk_next_ready & (chunk_next.mode != ChunkDescClear);
        mover_w_push = mover_aw_push;
    end

    // AR
    always_comb begin
        mover_ar_pop = 0;
        req_o.ar = '0;
        req_o.ar_valid = !mover_ar_empty;
        req_o.ar.addr = mover_ar.src_addr;
        req_o.ar.size = 3;
        req_o.ar.len = mover_ar.len;
        req_o.ar.id = (mover_ar.mode == ChunkDescRead ? 1 : 0);
        if (req_o.ar_valid && rsp_i.ar_ready) begin
            mover_ar_pop = 1;
        end
    end

    // R
    always_comb begin
        req_o.r_ready = 0;
        mover_r_push = 0;
        desc_read_data = rsp_i.r.data;
        desc_read_last = rsp_i.r.last;
        desc_read_valid = 0;
        if (rsp_i.r_valid) begin
            if (rsp_i.r.id == 1) begin
                req_o.r_ready = 1;
                desc_read_valid = 1;
            end else begin
                req_o.r_ready = ~mover_r_full;
                mover_r_push = req_o.r_ready;
            end
        end
    end

    // AW
    always_comb begin
        mover_aw_pop = 0;
        req_o.aw = '0;
        req_o.aw_valid = !mover_aw_empty;
        req_o.aw.addr = mover_aw.dst_addr;
        req_o.aw.size = 3;
        req_o.aw.len = mover_aw.len;
        req_o.aw.id = 0;
        if (req_o.aw_valid && rsp_i.aw_ready) begin
            mover_aw_pop = 1;
        end
    end

    // W
    always_comb begin
        mover_w_pop = 0;
        mover_r_pop = 0;
        req_o.w = '0;
        req_o.w.strb = '1;
        if (mover_w == ChunkDescClear) begin
            req_o.w.data = '0;
            req_o.w.last = 1;
            req_o.w_valid = 1;
            if (req_o.w_valid && rsp_i.w_ready) begin
                mover_w_pop = 1;
            end
        end else begin
            req_o.w.data = mover_r.data;
            req_o.w.last = mover_r.last;
            req_o.w_valid = ~mover_r_empty;
            if (req_o.w_valid && rsp_i.w_ready) begin
                mover_r_pop = 1;
                if (req_o.w.last) mover_w_pop = 1;
            end
        end
    end

    // B
    assign req_o.b_ready = 1;

endmodule
