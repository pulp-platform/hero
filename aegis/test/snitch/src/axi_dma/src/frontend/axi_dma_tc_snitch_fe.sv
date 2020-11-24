// Copyright (c) 2019 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Thomas Benz <tbenz@ethz.ch>

// Implements the tightly-coupled frontend. This module can directly be connected
// to an accelerator bus in the snitch system

module axi_dma_tc_snitch_fe #(
    parameter type         axi_req_t          = logic,
    parameter type         axi_res_t          = logic
) (
    input  logic           clk_i,
    input  logic           rst_ni,
    // AXI4 bus
    output axi_req_t       axi_dma_req_o,
    input  axi_res_t       axi_dma_res_i,
    // debug output
    output logic           dma_busy_o,
    // accelerator interface
    input  logic [31:0]    acc_qaddr_i,
    input  logic [ 4:0]    acc_qid_i,
    input  logic [31:0]    acc_qdata_op_i,
    input  logic [63:0]    acc_qdata_arga_i,
    input  logic [63:0]    acc_qdata_argb_i,
    input  logic [63:0]    acc_qdata_argc_i,
    input  logic           acc_qvalid_i,
    output logic           acc_qready_o,

    output logic [63:0]    acc_pdata_o,
    output logic [ 4:0]    acc_pid_o,
    output logic           acc_perror_o,
    output logic           acc_pvalid_o,
    input  logic           acc_pready_i,

    // hart id of the frankensnitch
    input  logic [31:0]       hart_id_i,

    // performance output
    output axi_dma_pkg::dma_perf_t dma_perf_o

);

    //--------------------------------------
    // Backend Instantiation
    //--------------------------------------
    logic                    backend_idle;
    logic                    oned_trans_complete;
    axi_dma_pkg::burst_req_t burst_req;
    logic                    burst_req_valid;
    logic                    burst_req_ready;

    axi_dma_backend #(
        .DataWidth           ( snitch_pkg::DmaDataWidth       ),
        .AddrWidth           ( snitch_pkg::DmaAddrWidth       ),
        .IdWidth             ( snitch_pkg::IdWidthDma         ),
        .TransFifoDepth      ( snitch_pkg::AxiDmaTfFifoDepth  ),
        .AxReqFifoDepth      ( snitch_pkg::AxiAxReqDepth      ),
        .burst_req_t         ( axi_dma_pkg::burst_req_t       ),
        .DmaIdWidth          ( 32                             ),
        .DmaTracing          ( snitch_pkg::DmaTracing         ),
        .BufferDepth         ( 3                              ), // don't change
        .axi_req_t           ( axi_req_t                      ),
        .axi_res_t           ( axi_res_t                      )
    ) i_axi_dma_backend (
        .clk_i            ( clk_i               ),
        .rst_ni           ( rst_ni              ),
        .axi_dma_req_o    ( axi_dma_req_o       ),
        .axi_dma_res_i    ( axi_dma_res_i       ),
        .burst_req_i      ( burst_req           ),
        .valid_i          ( burst_req_valid     ),
        .ready_o          ( burst_req_ready     ),
        .backend_idle_o   ( backend_idle        ),
        .trans_complete_o ( oned_trans_complete ),
        .dma_id_i         ( hart_id_i           )
    );

    // DMA is busy when it is not idle
    assign dma_busy_o = !backend_idle;

    //--------------------------------------
    // 2D Extension
    //--------------------------------------
    axi_dma_pkg::twod_req_t twod_req_d, twod_req_q;
    logic                   twod_req_valid;
    logic                   twod_req_ready;
    logic                   twod_req_last;

    axi_dma_twod_ext #(
        .ADDR_WIDTH       ( snitch_pkg::DmaAddrWidth        ),
        .REQ_FIFO_DEPTH   ( snitch_pkg::AxiDmaTwodFifoDepth )
    ) i_axi_dma_twod_ext (
        .clk_i                ( clk_i               ),
        .rst_ni               ( rst_ni              ),

        .burst_req_o          ( burst_req           ),
        .burst_req_valid_o    ( burst_req_valid     ),
        .burst_req_ready_i    ( burst_req_ready     ),

        .twod_req_i           ( twod_req_d          ),
        .twod_req_valid_i     ( twod_req_valid      ),
        .twod_req_ready_o     ( twod_req_ready      ),
        .twod_req_last_o      ( twod_req_last       )
    );

    //--------------------------------------
    // Buffer twod last
    //--------------------------------------
    localparam TWOD_BUFFER_DEPTH = 2 * snitch_pkg::AxiDmaTfFifoDepth +
        snitch_pkg::AxiAxReqDepth + 3 + 1;
    logic twod_req_last_realigned;
    fifo_v3 # (
        .DATA_WIDTH  (  1                 ),
        .DEPTH       ( TWOD_BUFFER_DEPTH  )
    ) i_fifo_v3_last_twod_buffer (
        .clk_i       ( clk_i                             ),
        .rst_ni      ( rst_ni                            ),
        .flush_i     ( 1'b0                              ),
        .testmode_i  ( 1'b0                              ),
        .full_o      ( ),
        .empty_o     ( ),
        .usage_o     ( ),
        .data_i      ( twod_req_last                     ),
        .push_i      ( burst_req_valid & burst_req_ready ),
        .data_o      ( twod_req_last_realigned           ),
        .pop_i       ( oned_trans_complete               )
    );

    //--------------------------------------
    // ID gen
    //--------------------------------------
    logic [31:0] next_id;
    logic [31:0] completed_id;

    axi_dma_tc_snitch_fe_id_gen #(
        .ID_WIDTH     ( 32     )
    ) i_axi_dma_tc_snitch_fe_id_gen (
        .clk_i        ( clk_i                                          ),
        .rst_ni       ( rst_ni                                         ),
        .issue_i      ( twod_req_valid && twod_req_ready               ),
        .retire_i     ( oned_trans_complete && twod_req_last_realigned ),
        .next_o       ( next_id                                        ),
        .completed_o  ( completed_id                                   )
    );

    //--------------------------------------
    // Performance counters
    //--------------------------------------
    axi_dma_perf_counters #(
        .TRANSFER_ID_WIDTH  ( 32                       ),
        .DATA_WIDTH         ( snitch_pkg::DmaDataWidth ),
        .axi_req_t          ( axi_req_t                ),
        .axi_res_t          ( axi_res_t                )
    ) i_axi_dma_perf_counters (
        .clk_i           ( clk_i               ),
        .rst_ni          ( rst_ni              ),
        .axi_dma_req_i   ( axi_dma_req_o       ),
        .axi_dma_res_i   ( axi_dma_res_i       ),
        .next_id_i       ( next_id             ),
        .completed_id_i  ( completed_id        ),
        .dma_busy_i      ( dma_busy_o          ),
        .dma_perf_o      ( dma_perf_o          )
    );

    //--------------------------------------
    // Spill register for response channel
    //--------------------------------------
    snitch_pkg::acc_resp_t dma_resp_d, dma_resp_q;
    logic acc_pvalid_spill;
    logic acc_pready_spill;

    // the response path needs to be decoupled
    spill_register #(
        .T            ( snitch_pkg::acc_resp_t )
    ) i_spill_register_dma_resp (
        .clk_i        ( clk_i              ),
        .rst_ni       ( rst_ni             ),
        .valid_i      ( acc_pvalid_spill   ),
        .ready_o      ( acc_pready_spill   ),
        .data_i       ( dma_resp_d         ),
        .valid_o      ( acc_pvalid_o       ),
        .ready_i      ( acc_pready_i       ),
        .data_o       ( dma_resp_q         )
    );

    //--------------------------------------
    // Instruction decode
    //--------------------------------------
    logic            is_dma_op;
    logic [12*8-1:0] dma_op_name;

    always_comb begin : proc_fe_inst_decode

        // defaults
        twod_req_d       = twod_req_q;
        twod_req_valid   = 1'b0;

        acc_qready_o     = 1'b0;

        dma_resp_d       =  '0;
        dma_resp_d.error = 1'b1;

        acc_pdata_o      = dma_resp_q.data;
        acc_pid_o        = dma_resp_q.id;
        acc_perror_o     = dma_resp_q.error;
        acc_pvalid_spill = 1'b0;

        // debug signal
        is_dma_op        = 1'b0;
        dma_op_name      = "Invalid";

        // decode
        unique casez (acc_qdata_op_i)

            // manipulate the source register
            riscv_instr::DM_SRC : begin
                if (acc_qvalid_i == 1'b1) begin
                    twod_req_d.src[31: 0] = acc_qdata_arga_i[31: 0];
                    twod_req_d.src[63:32] = acc_qdata_argb_i[31: 0];
                    acc_qready_o = 1'b1;
                    is_dma_op    = 1'b1;
                    dma_op_name  = "DM_SRC";
                end
            end

            // manipulate the destination register
            riscv_instr::DM_DST : begin
                if (acc_qvalid_i == 1'b1) begin
                    twod_req_d.dst[31: 0] = acc_qdata_arga_i[31: 0];
                    twod_req_d.dst[63:32] = acc_qdata_argb_i[31: 0];
                    acc_qready_o = 1'b1;
                    is_dma_op    = 1'b1;
                    dma_op_name  = "DM_DST";
                end
            end

            // start the DMA (immediate config)
            riscv_instr::DM_STRTI : begin

                // handshaking
                acc_pvalid_spill = twod_req_ready;

                if (acc_qvalid_i == 1'b1 && acc_pready_spill == 1'b1) begin
                    // read in config
                    twod_req_d.num_bytes   = acc_qdata_arga_i;
                    twod_req_d.decouple_rw = acc_qdata_op_i[25];
                    twod_req_d.is_twod     = acc_qdata_op_i[26];
                    twod_req_d.burst_src   = acc_qdata_op_i[28:27];
                    twod_req_d.burst_dst   = acc_qdata_op_i[30:29];
                    twod_req_d.deburst     = acc_qdata_op_i[31];
                    twod_req_valid         = 1'b1;
                    // response
                    dma_resp_d.id          = acc_qid_i;
                    dma_resp_d.data        = next_id;
                    dma_resp_d.error       = 1'b0;
                    // handshaking
                    acc_qready_o           = twod_req_ready;
                    is_dma_op              = 1'b1;
                    dma_op_name            = "DM_STRTI";
                end
            end

            // start the DMA (register config)
            riscv_instr::DM_STRT : begin

                // handshaking
                acc_pvalid_spill = twod_req_ready;

                if (acc_qvalid_i == 1'b1 && acc_pready_spill == 1'b1) begin
                    // read in config
                    twod_req_d.num_bytes   = acc_qdata_arga_i;
                    twod_req_d.decouple_rw = acc_qdata_argb_i[0];
                    twod_req_d.is_twod     = acc_qdata_argb_i[1];
                    twod_req_d.burst_src   = acc_qdata_argb_i[3:2];
                    twod_req_d.burst_dst   = acc_qdata_argb_i[5:4];
                    twod_req_d.deburst     = acc_qdata_argb_i[6];
                    twod_req_valid         = 1'b1;
                    // response
                    dma_resp_d.id          = acc_qid_i;
                    dma_resp_d.data        = next_id;
                    dma_resp_d.error       = 1'b0;
                    // handshaking
                    acc_qready_o           = twod_req_ready;
                    is_dma_op              = 1'b1;
                    dma_op_name            = "DM_STRT";
                end
            end

            // status of the DMA (immediate config)
            riscv_instr::DM_STATI : begin
                if (acc_qvalid_i == 1'b1 && acc_pready_spill == 1'b1) begin
                    // response
                    dma_resp_d.id               = acc_qid_i;
                    dma_resp_d.error            = 1'b0;
                    // response vary on content in register/immediate
                    case (acc_qdata_op_i[26:25])
                        2'b00 : dma_resp_d.data = completed_id;
                        2'b01 : dma_resp_d.data = next_id;
                        2'b10 : dma_resp_d.data = { {{8'd63}{1'b0}}, dma_busy_o };
                        // DMA reuest fifo is full
                        2'b11 : dma_resp_d.data = { {{8'd63}{1'b0}}, !twod_req_ready };
                    endcase
                    // handshaking
                    acc_pvalid_spill            = 1'b1;
                    acc_qready_o                = 1'b1;
                    is_dma_op                   = 1'b1;
                    dma_op_name                 = "DM_STATI";
                end
            end

            // status of the DMA (register config)
            riscv_instr::DM_STAT : begin
                if (acc_qvalid_i == 1'b1 && acc_pready_spill == 1'b1) begin
                    // response
                    dma_resp_d.id               = acc_qid_i;
                    dma_resp_d.error            = 1'b0;
                    // response vary on content in register/immediate
                    case (acc_qdata_arga_i[1:0])
                        2'b00 : dma_resp_d.data = completed_id;
                        2'b01 : dma_resp_d.data = next_id;
                        2'b10 : dma_resp_d.data = { {{8'd63}{1'b0}}, dma_busy_o };
                        2'b11 : dma_resp_d.data = { {{8'd63}{1'b0}}, dma_busy_o };
                    endcase
                    // handshaking
                    acc_pvalid_spill            = 1'b1;
                    acc_qready_o                = 1'b1;
                    is_dma_op                   = 1'b1;
                    dma_op_name                 = "DM_STAT";
                end
            end

            // error status of the DMA (immediate config)
            riscv_instr::DM_ERRI : begin
                if (acc_qvalid_i == 1'b1 && acc_pready_spill == 1'b1) begin
                    // response
                    dma_resp_d.id               = acc_qid_i;
                    dma_resp_d.error            = 1'b0;
                    // response vary on content in register/immediate
                    case (acc_qdata_op_i[25])
                        1'b0 : dma_resp_d.data  = '0;
                        1'b1 : dma_resp_d.data  = '0;
                    endcase
                    // handshaking
                    acc_pvalid_spill            = 1'b1;
                    acc_qready_o                = 1'b1;
                    is_dma_op                   = 1'b1;
                    dma_op_name                 = "DM_ERRI";
                end
            end

            // error status of the DMA (register config)
            riscv_instr::DM_ERR : begin

                acc_pvalid_spill           = 1'b1;

                if (acc_qvalid_i == 1'b1 && acc_pready_spill == 1'b1) begin
                    // response
                    dma_resp_d.id               = acc_qid_i;
                    dma_resp_d.error            = 1'b0;
                    // response vary on content in register/immediate
                    case (acc_qdata_arga_i[0])
                        1'b0 : dma_resp_d.data  = '0;
                        1'b1 : dma_resp_d.data  = '0;
                    endcase
                    // handshaking
                    acc_qready_o                = 1'b1;
                    is_dma_op                   = 1'b1;
                    dma_op_name                 = "DM_ERR";
                end
            end

            // manipulate the strides
            riscv_instr::DM_TWOD_STRD : begin
                if (acc_qvalid_i == 1'b1) begin
                    twod_req_d.stride_src = acc_qdata_arga_i;
                    twod_req_d.stride_dst = acc_qdata_argb_i;
                    acc_qready_o = 1'b1;
                    is_dma_op    = 1'b1;
                    dma_op_name  = "DM_TWOD_STRD";
                end
            end

            // manipulate the strides
            riscv_instr::DM_TWOD_REPS : begin
                if (acc_qvalid_i == 1'b1) begin
                    twod_req_d.num_repetitions = acc_qdata_arga_i;
                    acc_qready_o = 1'b1;
                    is_dma_op    = 1'b1;
                    dma_op_name  = "DM_TWOD_REPS";
                end
            end

            default : begin
            end

        endcase
    end

    //--------------------------------------
    // State
    //--------------------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_modifiable_request
        if(!rst_ni) begin
            twod_req_q <= '0;
        end else begin
            twod_req_q <= twod_req_d;
        end
    end

endmodule : axi_dma_tc_snitch_fe
