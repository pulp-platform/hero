// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Thomas Benz <tbenz@iis.ee.ethz.ch>

/// replaces the mchan in the pulp cluster if the new AXI DMA should be used
/// strictly 32 bit on the TCDM side.
module pulp_cluster_dma_frontend #(
    /// number of cores in the cluster
    parameter int unsigned NumCores       = -1,
    /// id width of peripherals
    parameter int unsigned PerifIdWidth   = -1,
    /// id width of the DMA AXI Master port
    parameter int unsigned DmaAxiIdWidth  = -1,
    /// data width of the DMA AXI Master port
    parameter int unsigned DmaDataWidth   = -1,
    /// address width of the DMA AXI Master port
    parameter int unsigned DmaAddrWidth   = -1,
    /// number of AX requests in-flight
    parameter int unsigned AxiAxReqDepth  = -1,
    /// number of 1D transfers buffered in backend
    parameter int unsigned TfReqFifoDepth = -1,
    /// data request type
    parameter type axi_req_t      = logic,
    /// data response type
    parameter type axi_res_t      = logic
)(
    input  logic                      clk_i,
    input  logic                      rst_ni,
    input logic [5:0]                 cluster_id_i,
    /// x-bar
    input  logic                      ctrl_pe_targ_req_i,
    input  logic                      ctrl_pe_targ_type_i,
    input  logic [3:0]                ctrl_pe_targ_be_i,
    input  logic [31:0]               ctrl_pe_targ_add_i,
    input  logic [31:0]               ctrl_pe_targ_data_i,
    input  logic [PerifIdWidth-1:0]   ctrl_pe_targ_id_i,
    output logic                      ctrl_pe_targ_gnt_o,
    output logic                      ctrl_pe_targ_r_valid_o,
    output logic [31:0]               ctrl_pe_targ_r_data_o,
    output logic                      ctrl_pe_targ_r_opc_o,
    output logic [PerifIdWidth-1:0]   ctrl_pe_targ_r_id_o,
    /// from cores
    input  logic [NumCores-1:0]       ctrl_targ_req_i,
    input  logic [NumCores-1:0]       ctrl_targ_type_i,
    input  logic [NumCores-1:0][3:0]  ctrl_targ_be_i,
    input  logic [NumCores-1:0][31:0] ctrl_targ_add_i,
    input  logic [NumCores-1:0][31:0] ctrl_targ_data_i,
    output logic [NumCores-1:0]       ctrl_targ_gnt_o,
    output logic [NumCores-1:0]       ctrl_targ_r_valid_o,
    output logic [NumCores-1:0][31:0] ctrl_targ_r_data_o,
    /// wide AXI port
    output axi_req_t                  axi_dma_req_o,
    input  axi_res_t                  axi_dma_res_i,
    /// status signal
    output logic                      busy_o,
    /// events and interrupts (cores)
    output logic [NumCores-1:0]       term_event_o,
    output logic [NumCores-1:0]       term_irq_o,
    /// events and interrupts (peripherals)
    output logic                      term_event_pe_o,
    output logic                      term_irq_pe_o
);

    // DMA transfer descriptor
    typedef struct packed {
        logic [31:0] num_bytes;
        logic [31:0] dst_addr;
        logic [31:0] src_addr;
        logic        deburst;
        logic        decouple;
        logic        serialize;
    } transf_descr_t;

    // generate registers for cores
    for (genvar i = 0; i < NumCores; i++) begin : gen_core_regs

        pulp_cluster_dma_frontend_regs #(
            .transf_descr_t ( transf_descr_t    )
        ) i_dma_conf_regs_cores (
            .clk_i          ( clk_i                   ),
            .rst_ni         ( rst_ni                  ),
            .ctrl_req_i     ( ctrl_targ_req_i     [i] ),
            .ctrl_type_i    ( ctrl_targ_type_i    [i] ),
            .ctrl_be_i      ( ctrl_targ_be_i      [i] ),
            .ctrl_add_i     ( ctrl_targ_add_i     [i] ),
            .ctrl_data_i    ( ctrl_targ_data_i    [i] ),
            .ctrl_gnt_o     ( ctrl_targ_gnt_o     [i] ),
            .ctrl_valid_o   ( ctrl_targ_r_valid_o [i] ),
            .ctrl_data_o    ( ctrl_targ_r_data_o  [i] ),
            .next_id_i      ( ),
            .done_id_i      ( ),
            .be_ready_i     ( ),
            .be_valid_o     ( ),
            .be_busy_i      ( ),
            .transf_descr_o ( )
        );
    end // gen_core_regs

    // generate registers for peripherals
    pulp_cluster_dma_frontend_regs #(
        .transf_descr_t ( transf_descr_t    )
    ) i_dma_conf_regs_periphs (
        .clk_i          ( clk_i                             ),
        .rst_ni         ( rst_ni                            ),
        .ctrl_req_i     ( ctrl_pe_targ_req_i                ),
        .ctrl_type_i    ( ctrl_pe_targ_type_i               ),
        .ctrl_be_i      ( ctrl_pe_targ_be_i                 ),
        .ctrl_add_i     ( ctrl_pe_targ_add_i                ),
        .ctrl_data_i    ( ctrl_pe_targ_data_i               ),
        .ctrl_gnt_o     ( ctrl_pe_targ_gnt_o                ),
        .ctrl_valid_o   ( ctrl_pe_targ_r_valid_o            ),
        .ctrl_data_o    ( ctrl_pe_targ_r_data_o             ),
        .next_id_i      ( ),
        .done_id_i      ( ),
        .be_ready_i     ( ),
        .be_valid_o     ( ),
        .be_busy_i      ( ),
        .transf_descr_o ( )
    );

endmodule : pulp_cluster_dma_frontend
