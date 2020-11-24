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

/// A protocol adapter from the preipheral bus to REQRSP.
module peripherals_to_reqrsp #(
    /// The address width. >=1.
    parameter int AW = -1,
    /// The data width. >=1.
    parameter int DW = -1,
    /// The ID width. >=0.
    parameter int IW = -1
)(
    input  logic            clk_i               ,
    input  logic            rst_ni              ,

    input  logic [AW-1:0]   peripherals_add     ,
    input  logic            peripherals_wen     ,
    input  logic [DW-1:0]   peripherals_wdata   ,
    input  logic [DW/8-1:0] peripherals_be      ,
    input  logic [IW-1:0]   peripherals_id      ,
    input  logic            peripherals_req     ,
    output logic            peripherals_gnt     ,
    output logic [DW-1:0]   peripherals_r_rdata ,
    output logic            peripherals_r_opc   ,
    output logic [IW-1:0]   peripherals_r_id    ,
    output logic            peripherals_r_valid ,

    REQRSP_BUS.out          reqrsp_o
);

    // Check invariants.
    `ifndef SYNTHESIS
    initial begin
        assert(AW > 0);
        assert(DW > 0);
        assert(IW >= 0);
        assert(reqrsp_o.ADDR_WIDTH >= AW);
        assert(reqrsp_o.DATA_WIDTH == DW);
        assert(reqrsp_o.ID_WIDTH   >= IW);
    end
    `endif

    // Translate incoming requests from the peripherals.
    always_comb begin : p_req
        reqrsp_o.qaddr  = peripherals_add;
        reqrsp_o.qwrite = ~peripherals_wen;
        reqrsp_o.qdata  = peripherals_wdata;
        reqrsp_o.qstrb  = peripherals_be;
        reqrsp_o.qid    = peripherals_id;
        reqrsp_o.qvalid = peripherals_req;
        peripherals_gnt = reqrsp_o.qready & peripherals_req;
    end

    // Translate outgoing responses to the peripherals.
    always_comb begin : p_rsp
        peripherals_r_rdata = reqrsp_o.pdata;
        peripherals_r_opc   = reqrsp_o.perror;
        peripherals_r_id    = reqrsp_o.pid;
        peripherals_r_valid = reqrsp_o.pvalid;
        reqrsp_o.pready     = 1;
    end

endmodule
