/// Description: Governs atomic memory oeprations. This module needs to be instantiated
/// in front of an SRAM. It needs to have exclusive access over it.

/// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
`include "common_cells/registers.svh"

module amo_shim #(
    parameter int unsigned AddrMemWidth = 32,
    parameter bit          RegisterAmo  = 1'b0 // Cut path between request and response at the cost of increased AMO latency
) (
    input   logic                     clk_i,
    input   logic                     rst_ni,
    // master side
    input   logic                     in_req_i,       // Bank request
    output  logic                     in_gnt_o,       // Bank grant
    input   logic [AddrMemWidth-1:0]  in_add_i,       // Address
    input   logic [3:0]               in_amo_i,       // Atomic Memory Operation
    input   logic                     in_wen_i,       // 1: Store, 0: Load
    input   logic [63:0]              in_wdata_i,     // Write data
    input   logic [7:0]               in_be_i,        // Byte enable
    output  logic [63:0]              in_rdata_o,     // Read data
    // slave side
    output  logic                     out_req_o,      // Bank request
    output  logic [AddrMemWidth-1:0]  out_add_o,      // Address
    output  logic                     out_wen_o,      // 1: Store, 0: Load
    output  logic [63:0]              out_wdata_o,    // Write data
    output  logic [7:0]               out_be_o,       // Byte enable
    input   logic [63:0]              out_rdata_i,    // Read data
    // dma ports  
    input   logic                     dma_access_i,   // Current Access is a DMA access -> bypass amo, abort current op
    output  logic                     amo_conflict_o  // Throw an error if DMA access occured on amo mem location
);

    typedef enum logic [3:0] {
        AMONone = 4'h0,
        AMOSwap = 4'h1,
        AMOAdd  = 4'h2,
        AMOAnd  = 4'h3,
        AMOOr   = 4'h4,
        AMOXor  = 4'h5,
        AMOMax  = 4'h6,
        AMOMaxu = 4'h7,
        AMOMin  = 4'h8,
        AMOMinu = 4'h9,
        AMOLR   = 4'hA,
        AMOSC   = 4'hB
    } amo_op_t;

    enum logic [1:0] {
        Idle, DoAMO, WriteBackAMO, ProlongAMO
    } state_q, state_d, state_qq;

    amo_op_t     amo_op_q, amo_op_qq;

    logic        load_amo;

    logic [AddrMemWidth-1:0] addr_q;

    logic [31:0] amo_operand_a;
    logic [31:0] amo_operand_a_d, amo_operand_a_q;
    logic [31:0] amo_operand_b_q;
    // requested amo should be performed on upper 32 bit
    logic        upper_word_q;
    logic [31:0] swap_value_q;
    logic [31:0] amo_result, amo_result_q; // result of atomic memory operation
    logic [31:0] amo_result_prolong_q; // in the case of an interfering DMA transfer -> save result

    always_comb begin
        // feed-through
        out_req_o   = in_req_i;
        in_gnt_o    = in_req_i;
        out_add_o   = in_add_i;
        out_wen_o   = in_wen_i;
        out_wdata_o = in_wdata_i;
        out_be_o    = in_be_i;
        in_rdata_o  = out_rdata_i;

        // assume no error happened
        amo_conflict_o = 1'b0;

        state_d     = state_q;
        load_amo = 1'b0;
        amo_operand_a   = upper_word_q ? out_rdata_i[63:32] : out_rdata_i[31:0];
        amo_operand_a_d = amo_operand_a;

        unique case (state_q)
            Idle: begin
                if (in_req_i && amo_op_t'(in_amo_i) != AMONone) begin
                    load_amo = 1'b1;
                    state_d = DoAMO;
                end
            end
            // Claim the memory interface
            DoAMO, WriteBackAMO: begin

                // check if amo op was prolonged, if so use previous results
                if(state_qq == ProlongAMO) begin
                    amo_operand_a = amo_operand_a_q;
                end

                in_gnt_o    = 1'b0;
                state_d     = (RegisterAmo && state_q != WriteBackAMO) ?  WriteBackAMO : Idle;
                // Commit AMO
                out_req_o   = 1'b1;
                out_wen_o   = 1'b1;
                out_add_o   = addr_q;
                // shift up if the address was pointing to the upper 32 bits
                out_be_o    = (upper_word_q ?  8'b1111_0000 : 8'b0000_1111);
                // serve from register if we cut the path
                if (RegisterAmo) begin
                    out_wdata_o = (upper_word_q ? {amo_result_q, 32'b0} : {32'b0, amo_result_q});
                end else begin
                    out_wdata_o = (upper_word_q ? {amo_result, 32'b0} : {32'b0, amo_result});
                end
                in_rdata_o  = upper_word_q ? {amo_operand_a, 32'b0} : {32'b0, amo_operand_a};
                // overrule amo shim if dma is active
                if (dma_access_i) begin
                    out_req_o      = in_req_i;
                    in_gnt_o       = in_req_i;
                    out_add_o      = in_add_i;
                    out_wen_o      = in_wen_i;
                    out_wdata_o    = in_wdata_i;
                    out_be_o       = in_be_i;
                    in_rdata_o     = out_rdata_i;
                    // something dangerous happend, inform programmer
                    amo_conflict_o = (addr_q == in_add_i);
                    // prolong the amo state
                    state_d        = ProlongAMO;
                end
            end
            // AMO was interrupted by DMA transfer and therefore prolonged
            ProlongAMO: begin
                state_d         = dma_access_i ? ProlongAMO : WriteBackAMO;
                amo_operand_a_d = amo_operand_a_q;
            end

            default:;
        endcase
    end

    if (RegisterAmo) begin : gen_amo_slice
        `FFLNR(amo_result_q, amo_result, (state_q == DoAMO), clk_i)
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            state_q         <= Idle;
            amo_op_q        <= amo_op_t'('0);
            addr_q          <= '0;
            amo_operand_b_q <= '0;
            amo_operand_a_q <= '0;
            swap_value_q    <= '0;
            upper_word_q    <= '0;
            amo_op_qq       <= amo_op_t'('0);
        end else begin
            state_q         <= state_d;
            state_qq        <= state_q;
            amo_op_qq       <= amo_op_q;
            amo_operand_a_q <= amo_operand_a_d;
            if (load_amo) begin
                amo_op_q        <= amo_op_t'(in_amo_i);
                addr_q          <= in_add_i;
                amo_operand_b_q <= in_be_i[0] ? in_wdata_i[31:0]  : in_wdata_i[63:32];
                // swap value is located in the upper word
                swap_value_q    <= in_be_i[0] ? in_wdata_i[63:32] : in_wdata_i[63:32];
                upper_word_q    <= in_be_i[4];
            // on DMA access, keep last op in memory
            end else if (dma_access_i) begin
                amo_op_q        <= amo_op_q;
            end else begin
                amo_op_q        <= AMONone;
            end
        end
    end

    // ----------------
    // AMO ALU
    // ----------------
    logic [33:0] adder_sum;
    logic [32:0] adder_operand_a, adder_operand_b;

    assign adder_sum = adder_operand_a + adder_operand_b;
    /* verilator lint_off WIDTH */
    always_comb begin : amo_alu

        adder_operand_a = $signed(amo_operand_a);
        adder_operand_b = $signed(amo_operand_b_q);

        amo_result = amo_operand_b_q;

        unique case (state_qq == ProlongAMO ? amo_op_qq : amo_op_q)
            // the default is to output operand_b
            AMOSwap:;
            AMOAdd: amo_result = adder_sum[31:0];
            AMOAnd: amo_result = amo_operand_a & amo_operand_b_q;
            AMOOr:  amo_result = amo_operand_a | amo_operand_b_q;
            AMOXor: amo_result = amo_operand_a ^ amo_operand_b_q;
            AMOMax: begin
                adder_operand_b = -$signed(amo_operand_b_q);
                amo_result = adder_sum[32] ? amo_operand_b_q : amo_operand_a;
            end
            AMOMin: begin
                adder_operand_b = -$signed(amo_operand_b_q);
                amo_result = adder_sum[32] ? amo_operand_a : amo_operand_b_q;
            end
            AMOMaxu: begin
                adder_operand_a = $unsigned(amo_operand_a);
                adder_operand_b = -$unsigned(amo_operand_b_q);
                amo_result = adder_sum[32] ? amo_operand_b_q : amo_operand_a;
            end
            AMOMinu: begin
                adder_operand_a = $unsigned(amo_operand_a);
                adder_operand_b = -$unsigned(amo_operand_b_q);
                amo_result = adder_sum[32] ? amo_operand_a : amo_operand_b_q;
            end
            default: amo_result = '0;
        endcase
    end
    /* verilator lint_on WIDTH */
endmodule
