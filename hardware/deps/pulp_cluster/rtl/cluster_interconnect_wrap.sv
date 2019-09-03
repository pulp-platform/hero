// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/*
 * cluster_interconnect_wrap.sv
 * Davide Rossi <davide.rossi@unibo.it>
 * Antonio Pullini <pullinia@iis.ee.ethz.ch>
 * Igor Loi <igor.loi@unibo.it>
 * Francesco Conti <fconti@iis.ee.ethz.ch>
 */
 
module cluster_interconnect_wrap
#(
  parameter NB_CORES        = 8,
  parameter NB_HWACC_PORTS  = 4,
  parameter NB_DMAS         = 4,
  parameter NB_MPERIPHS     = 1,
  parameter NB_TCDM_BANKS   = 16,
  parameter NB_SPERIPHS     = 3,
  parameter DATA_WIDTH      = 32,
  parameter ADDR_WIDTH      = 32,
  parameter BE_WIDTH        = DATA_WIDTH/8,
  //TCDM PARAMETERS
  parameter TEST_SET_BIT    = 20,
  parameter ADDR_MEM_WIDTH  = 11,
  parameter LOG_CLUSTER     = 5,
  parameter PE_ROUTING_LSB  = 16,
  parameter PE_ROUTING_MSB  = 19,
  parameter CLUSTER_ALIAS      = 1'b0,
  parameter CLUSTER_ALIAS_BASE = 12'h000
)
(
  input logic                          clk_i,
  input logic                          rst_ni,
  XBAR_TCDM_BUS.Slave                  core_tcdm_slave[NB_CORES+NB_HWACC_PORTS-1:0],
  input logic [NB_CORES-1:0][5:0]      core_tcdm_slave_atop,
  XBAR_PERIPH_BUS.Slave                core_periph_slave[NB_CORES-1:0],
  input logic [NB_CORES-1:0][5:0]      core_periph_slave_atop,
  XBAR_TCDM_BUS.Slave                  ext_slave[NB_DMAS-1:0],
  XBAR_TCDM_BUS.Slave                  dma_slave[NB_DMAS-1:0],
  XBAR_TCDM_BUS.Slave                  mperiph_slave[NB_MPERIPHS-1:0],
  TCDM_BANK_MEM_BUS.Master             tcdm_sram_master[NB_TCDM_BANKS-1:0],
  XBAR_PERIPH_BUS.Master               speriph_master[NB_SPERIPHS-1:0],
  output logic [NB_SPERIPHS-1:0][5:0]  speriph_master_atop,
  input logic [1:0]                    TCDM_arb_policy_i
);

  localparam TCDM_ID_WIDTH = NB_CORES+NB_DMAS+4+NB_HWACC_PORTS;

  // DMA --> LOGARITHMIC INTERCONNECT BUS SIGNALS
  logic [4+NB_DMAS-1:0][DATA_WIDTH-1:0] s_dma_bus_wdata;
  logic [4+NB_DMAS-1:0][ADDR_WIDTH-1:0] s_dma_bus_add;
  logic [4+NB_DMAS-1:0]                 s_dma_bus_req;
  logic [4+NB_DMAS-1:0]                 s_dma_bus_wen;
  logic [4+NB_DMAS-1:0][BE_WIDTH-1:0]   s_dma_bus_be;
  logic [4+NB_DMAS-1:0]                 s_dma_bus_gnt;
  logic [4+NB_DMAS-1:0][DATA_WIDTH-1:0] s_dma_bus_r_rdata;
  logic [4+NB_DMAS-1:0]                 s_dma_bus_r_valid;

  // MASTER PERIPHERALS --> PERIPHERAL INTERCONNECT BUS SIGNALS
  logic [NB_MPERIPHS-1:0][DATA_WIDTH-1:0] s_mperiph_bus_wdata;
  logic [NB_MPERIPHS-1:0][ADDR_WIDTH-1:0] s_mperiph_bus_add;
  logic [NB_MPERIPHS-1:0]                 s_mperiph_bus_req;
  logic [NB_MPERIPHS-1:0]                 s_mperiph_bus_wen;
  logic [NB_MPERIPHS-1:0][BE_WIDTH-1:0]   s_mperiph_bus_be;
  logic [NB_MPERIPHS-1:0]                 s_mperiph_bus_gnt  ;
  logic [NB_MPERIPHS-1:0]                 s_mperiph_bus_r_opc;
  logic [NB_MPERIPHS-1:0][DATA_WIDTH-1:0] s_mperiph_bus_r_rdata;
  logic [NB_MPERIPHS-1:0]                 s_mperiph_bus_r_valid;

  // DEMUX --> LOGARITHMIC INTERCONNECT BUS SIGNALS
  logic [NB_CORES+NB_HWACC_PORTS-1:0][DATA_WIDTH-1:0] s_core_tcdm_bus_wdata;
  logic [NB_CORES+NB_HWACC_PORTS-1:0][ADDR_WIDTH-1:0] s_core_tcdm_bus_add;
  logic [NB_CORES+NB_HWACC_PORTS-1:0]                 s_core_tcdm_bus_req;
  logic [NB_CORES+NB_HWACC_PORTS-1:0]                 s_core_tcdm_bus_wen;
  logic [NB_CORES+NB_HWACC_PORTS-1:0][BE_WIDTH-1:0]   s_core_tcdm_bus_be;
  logic [NB_CORES+NB_HWACC_PORTS-1:0]                 s_core_tcdm_bus_gnt;
  logic [NB_CORES+NB_HWACC_PORTS-1:0][DATA_WIDTH-1:0] s_core_tcdm_bus_r_rdata;
  logic [NB_CORES+NB_HWACC_PORTS-1:0]                 s_core_tcdm_bus_r_valid;

  // DEMUX -->  PERIPHERAL INTERCONNECT BUS SIGNALS
  logic [NB_CORES-1:0][ADDR_WIDTH-1:0] s_core_periph_bus_add;
  logic [NB_CORES-1:0]                 s_core_periph_bus_req;
  logic [NB_CORES-1:0][DATA_WIDTH-1:0] s_core_periph_bus_wdata;
  logic [NB_CORES-1:0]                 s_core_periph_bus_wen;
  logic [NB_CORES-1:0][5:0]            s_core_periph_bus_atop;
  logic [NB_CORES-1:0][BE_WIDTH-1:0]   s_core_periph_bus_be;
  logic [NB_CORES-1:0]                 s_core_periph_bus_gnt;
  logic [NB_CORES-1:0]                 s_core_periph_bus_r_opc;
  logic [NB_CORES-1:0]                 s_core_periph_bus_r_valid;
  logic [NB_CORES-1:0][DATA_WIDTH-1:0] s_core_periph_bus_r_rdata;

  // LOGARITHMIC INTERCONNECT --> AMO Shims
  logic [NB_TCDM_BANKS-1:0][ADDR_MEM_WIDTH-1:0] s_tcdm_bus_amo_shim_add;
  logic [NB_TCDM_BANKS-1:0]                     s_tcdm_bus_amo_shim_req;
  logic [NB_TCDM_BANKS-1:0]                     s_tcdm_bus_amo_shim_gnt;
  logic [NB_TCDM_BANKS-1:0]                     s_tcdm_bus_amo_shim_wen;
  logic [NB_TCDM_BANKS-1:0][BE_WIDTH-1:0]       s_tcdm_bus_amo_shim_be;

  // PERIPHERAL INTERCONNECT INTERCONNECT --> SLAVE PERIPHERALS BUS SIGNALS
  logic [NB_SPERIPHS-1:0][DATA_WIDTH-1:0]           s_speriph_bus_wdata;
  logic [NB_SPERIPHS-1:0][ADDR_WIDTH-1:0]           s_speriph_bus_add;
  logic [NB_SPERIPHS-1:0]                           s_speriph_bus_req;
  logic [NB_SPERIPHS-1:0]                           s_speriph_bus_wen;
  logic [NB_SPERIPHS-1:0][5:0]                      s_speriph_bus_atop;
  logic [NB_SPERIPHS-1:0][BE_WIDTH-1:0]             s_speriph_bus_be;
  logic [NB_SPERIPHS-1:0][NB_CORES+NB_MPERIPHS-1:0] s_speriph_bus_id;
  logic [NB_SPERIPHS-1:0]                           s_speriph_bus_gnt  ;
  logic [NB_SPERIPHS-1:0]                           s_speriph_bus_r_opc;
  logic [NB_SPERIPHS-1:0][NB_CORES+NB_MPERIPHS-1:0] s_speriph_bus_r_id;
  logic [NB_SPERIPHS-1:0][DATA_WIDTH-1:0]           s_speriph_bus_r_rdata;
  logic [NB_SPERIPHS-1:0]                           s_speriph_bus_r_valid;

  //********************************************************
  //****** BINDING INTERFACES TO INTERNAL BUS SINGALS ******
  //********************************************************
  generate
    for (genvar i=0; i<NB_CORES; i++) begin : CORE_PERIPH_BIND
      assign s_core_periph_bus_add[i]      =  core_periph_slave[i].add;
      assign s_core_periph_bus_req[i]      =  core_periph_slave[i].req;
      assign s_core_periph_bus_wdata[i]    =  core_periph_slave[i].wdata;
      assign s_core_periph_bus_wen[i]      =  core_periph_slave[i].wen;
      assign s_core_periph_bus_atop[i]     =  core_periph_slave_atop[i];
      assign s_core_periph_bus_be[i]       =  core_periph_slave[i].be;

      assign core_periph_slave[i].gnt      =  s_core_periph_bus_gnt[i];
      assign core_periph_slave[i].r_opc    =  s_core_periph_bus_r_opc[i];
      assign core_periph_slave[i].r_valid  =  s_core_periph_bus_r_valid[i];
      assign core_periph_slave[i].r_rdata  =  s_core_periph_bus_r_rdata[i];
    end // block: CORE_PERIPH_BIND
  endgenerate

  generate
    for (genvar i=0; i<NB_CORES+NB_HWACC_PORTS; i++) begin : CORE_TCDM_BIND
      assign s_core_tcdm_bus_add[i]      = core_tcdm_slave[i].add;
      assign s_core_tcdm_bus_req[i]      = core_tcdm_slave[i].req;
      assign s_core_tcdm_bus_wdata[i]    = core_tcdm_slave[i].wdata;
      assign s_core_tcdm_bus_wen[i]      = core_tcdm_slave[i].wen;
      assign s_core_tcdm_bus_be[i]       = core_tcdm_slave[i].be;

      assign core_tcdm_slave[i].gnt      = s_core_tcdm_bus_gnt[i];
      assign core_tcdm_slave[i].r_valid  = s_core_tcdm_bus_r_valid[i];
      assign core_tcdm_slave[i].r_rdata  = s_core_tcdm_bus_r_rdata[i];
    end // block: CORE_TCDM_BIND
  endgenerate

  generate
    for (genvar i=0; i<NB_DMAS; i++) begin : AXI2MEM_BIND
      assign s_dma_bus_add[i]      = ext_slave[i].add;
      assign s_dma_bus_req[i]      = ext_slave[i].req;
      assign s_dma_bus_wdata[i]    = ext_slave[i].wdata;
      assign s_dma_bus_wen[i]      = ext_slave[i].wen;
      assign s_dma_bus_be[i]       = ext_slave[i].be;

      assign ext_slave[i].gnt      = s_dma_bus_gnt[i];
      assign ext_slave[i].r_valid  = s_dma_bus_r_valid[i];
      assign ext_slave[i].r_rdata  = s_dma_bus_r_rdata[i];
    end
  endgenerate

  generate
    for (genvar i=0; i<NB_DMAS; i++) begin : DMAS_BIND
      // +4 takes into account the 4 ports used in axi2mem
      assign s_dma_bus_add[i+4]    = dma_slave[i].add;
      assign s_dma_bus_req[i+4]    = dma_slave[i].req;
      assign s_dma_bus_wdata[i+4]  = dma_slave[i].wdata;
      assign s_dma_bus_wen[i+4]    = dma_slave[i].wen;
      assign s_dma_bus_be[i+4]     = dma_slave[i].be;

      assign dma_slave[i].gnt      = s_dma_bus_gnt[i+NB_DMAS];
      assign dma_slave[i].r_valid  = s_dma_bus_r_valid[i+NB_DMAS];
      assign dma_slave[i].r_rdata  = s_dma_bus_r_rdata[i+NB_DMAS];
    end
  endgenerate

  generate
    for (genvar i=0; i<NB_MPERIPHS; i++) begin : MPERIPHS_BIND
      assign s_mperiph_bus_add[i]      = mperiph_slave[i].add;
      assign s_mperiph_bus_req[i]      = mperiph_slave[i].req;
      assign s_mperiph_bus_wdata[i]    = mperiph_slave[i].wdata;
      assign s_mperiph_bus_wen[i]      = mperiph_slave[i].wen;
      assign s_mperiph_bus_be[i]       = mperiph_slave[i].be;

      assign mperiph_slave[i].gnt      = s_mperiph_bus_gnt[i];
      assign mperiph_slave[i].r_opc    = s_mperiph_bus_r_opc[i];
      assign mperiph_slave[i].r_valid  = s_mperiph_bus_r_valid[i];
      assign mperiph_slave[i].r_rdata  = s_mperiph_bus_r_rdata[i];
    end // block: MPERIPHS_BIND
  endgenerate

  generate
    for (genvar i=0; i<NB_SPERIPHS; i++) begin : SPERIPHS_BIND
      assign speriph_master[i].add       = s_speriph_bus_add[i];
      assign speriph_master[i].req       = s_speriph_bus_req[i];
      assign speriph_master[i].wdata     = s_speriph_bus_wdata[i];
      assign speriph_master[i].wen       = s_speriph_bus_wen[i];
      assign speriph_master_atop[i]      = s_speriph_bus_atop[i];
      assign speriph_master[i].be        = s_speriph_bus_be[i];
      assign speriph_master[i].id        = s_speriph_bus_id[i];

      assign s_speriph_bus_gnt[i]        = speriph_master[i].gnt;
      assign s_speriph_bus_r_id[i]       = speriph_master[i].r_id;
      assign s_speriph_bus_r_opc[i]      = speriph_master[i].r_opc;
      assign s_speriph_bus_r_valid[i]    = speriph_master[i].r_valid;
      assign s_speriph_bus_r_rdata[i]    = speriph_master[i].r_rdata;
    end // block: SPERIPHS_BIND
  endgenerate

  localparam NUM_TCDM_ICONN_IN = NB_CORES + NB_HWACC_PORTS + NB_DMAS + 4;
  typedef struct packed {
    logic [DATA_WIDTH-1:0]  data;
    logic [5:0]             atop;
  } tcdm_data_t;
  tcdm_data_t [NUM_TCDM_ICONN_IN-1:0] iconn_inp_wdata, iconn_inp_rdata,
                                      iconn_oup_wdata, iconn_oup_rdata;
  tcdm_interconnect #(
    .NumIn        ( NUM_TCDM_ICONN_IN           ),
    .NumOut       ( NB_TCDM_BANKS               ),
    .AddrWidth    ( ADDR_WIDTH                  ),
    .DataWidth    ( $bits(tcdm_data_t)          ),
    .ByteOffWidth ( $clog2(DATA_WIDTH-1)-3      ), // determine byte offset from real data width
    .AddrMemWidth ( ADDR_MEM_WIDTH              ),
    .WriteRespOn  ( 1                           ),
    .RespLat      ( 1                           ),
    .Topology     ( tcdm_interconnect_pkg::LIC  )
  ) i_tcdm_interconnect (
    .clk_i,
    .rst_ni,

    .req_i    ( { s_dma_bus_req,      s_core_tcdm_bus_req}      ),
    .add_i    ( { s_dma_bus_add,      s_core_tcdm_bus_add}      ),
    .wen_i    ( { s_dma_bus_wen,      s_core_tcdm_bus_wen}      ),
    .wdata_i  ( iconn_inp_wdata                                 ),
    .be_i     ( { s_dma_bus_be,       s_core_tcdm_bus_be}       ),
    .gnt_o    ( { s_dma_bus_gnt,      s_core_tcdm_bus_gnt}      ),
    .vld_o    ( { s_dma_bus_r_valid,  s_core_tcdm_bus_r_valid}  ),
    .rdata_o  ( iconn_inp_rdata                                 ),

    .req_o    ( s_tcdm_bus_amo_shim_req   ),
    .gnt_i    ( s_tcdm_bus_amo_shim_gnt   ),
    .add_o    ( s_tcdm_bus_amo_shim_add   ),
    .wen_o    ( s_tcdm_bus_amo_shim_wen   ),
    .wdata_o  ( iconn_oup_wdata           ),
    .be_o     ( s_tcdm_bus_amo_shim_be    ),
    .rdata_i  ( iconn_oup_rdata           )
  );
  for (genvar i = 0; i < NUM_TCDM_ICONN_IN; i++) begin : gen_iconn_pack_inp_data
    if (i < NB_CORES + NB_HWACC_PORTS) begin
      assign iconn_inp_wdata[i].data = s_core_tcdm_bus_wdata[i];
      assign s_core_tcdm_bus_r_rdata[i] = iconn_inp_rdata[i].data;
    end else begin
      assign iconn_inp_wdata[i].data = s_dma_bus_wdata[i - (NB_CORES + NB_HWACC_PORTS)];
      assign s_dma_bus_r_rdata[i - (NB_CORES + NB_HWACC_PORTS)] = iconn_inp_rdata[i].data;
    end
    if (i < NB_CORES) begin
      assign iconn_inp_wdata[i].atop = core_tcdm_slave_atop[i];
    end else begin
      assign iconn_inp_wdata[i].atop = '0;
    end
  end

  for (genvar i = 0; i < NB_TCDM_BANKS; i++) begin : gen_amo_shim
    // Map ATOPs by RI5CYs to AMOs.
    logic [DATA_WIDTH-1:0] data;
    logic [5:0] atop;
    logic [3:0] amo;
    assign atop = iconn_oup_wdata[i].atop;
    always_comb begin
      data = iconn_oup_wdata[i].data;
      if (atop[5]) begin
        casex (atop[4:0])
          5'b00000: amo = 4'h2; // AMOAdd
          5'b00001: amo = 4'h1; // AMOSwap
          5'b0001x: $error("Unsupported LR/SC on L1!");
          default: begin
            assert (atop[1:0] == '0) else $error("Illegal AMO!");
            case (atop[4:2])
              3'b001: amo = 4'h5; // AMOXor
              3'b010: amo = 4'h4; // AMOOr
              3'b011: amo = 4'h3; // AMOAnd
              3'b100: amo = 4'h8; // AMOMin
              3'b101: amo = 4'h6; // AMOMax
              3'b110: amo = 4'h9; // AMOMinu
              3'b111: amo = 4'h7; // AMOMaxu
            endcase
          end
        endcase
      end else begin
        amo = 4'h0; // AMONone
      end
    end
    logic write_enable;
    logic [ADDR_MEM_WIDTH+2-1:0] addr;
    amo_shim #(
      .AddrMemWidth (ADDR_MEM_WIDTH+2),
      .DataWidth    (DATA_WIDTH)
    ) i_amo_shim (
      .clk_i,
      .rst_ni,

      .in_req_i     (s_tcdm_bus_amo_shim_req[i]),
      .in_gnt_o     (s_tcdm_bus_amo_shim_gnt[i]),
      .in_add_i     ({s_tcdm_bus_amo_shim_add[i], 2'b00}),
      .in_amo_i     (amo),
      .in_wen_i     (~s_tcdm_bus_amo_shim_wen[i]), // 0 = write, 1 = read
      .in_wdata_i   (data),
      .in_be_i      (s_tcdm_bus_amo_shim_be[i]),
      .in_rdata_o   (iconn_oup_rdata[i].data),

      .out_req_o    (tcdm_sram_master[i].req),
      .out_add_o    (addr),
      .out_wen_o    (write_enable),
      .out_wdata_o  (tcdm_sram_master[i].wdata),
      .out_be_o     (tcdm_sram_master[i].be),
      .out_rdata_i  (tcdm_sram_master[i].rdata)
    );
    assign iconn_oup_rdata[i].atop = '0;
    always_comb begin
      tcdm_sram_master[i].add = '0;
      tcdm_sram_master[i].add[ADDR_MEM_WIDTH-1:0] = addr[ADDR_MEM_WIDTH+2-1:2];
    end
    assign tcdm_sram_master[i].wen = ~write_enable;
  end

  // peripheral logarithmic interconnect
  XBAR_PE #(
    .N_CH0              ( NB_CORES             ),
    .N_CH1              ( NB_MPERIPHS          ),
    .N_SLAVE            ( NB_SPERIPHS          ),
    .ID_WIDTH           ( NB_CORES+NB_MPERIPHS ),
    .PE_LSB             ( 0                    ),
    .PE_MSB             ( ADDR_WIDTH-1         ),
    .LOG_CLUSTER        ( LOG_CLUSTER          ),
    .ADDR_WIDTH         ( ADDR_WIDTH           ),
    .DATA_WIDTH         ( DATA_WIDTH           ),
    .BE_WIDTH           ( BE_WIDTH             ),
    .PE_ROUTING_LSB     ( PE_ROUTING_LSB       ),
    .PE_ROUTING_MSB     ( PE_ROUTING_MSB       ),
    .CLUSTER_ALIAS      ( CLUSTER_ALIAS        ),
    .CLUSTER_ALIAS_BASE ( CLUSTER_ALIAS_BASE   )
  ) xbar_pe_inst (
    .clk              ( clk_i                                                   ),
    .rst_n            ( rst_ni                                                  ),
    .CLUSTER_ID       ( 5'b00000                                                ),
    .data_req_i       ( {s_mperiph_bus_req,         s_core_periph_bus_req}      ),
    .data_add_i       ( {s_mperiph_bus_add,         s_core_periph_bus_add}      ),
    .data_wen_i       ( {s_mperiph_bus_wen,         s_core_periph_bus_wen}      ),
    .data_atop_i      ( {{NB_MPERIPHS{6'b000000}},  s_core_periph_bus_atop}     ),
    .data_wdata_i     ( {s_mperiph_bus_wdata,       s_core_periph_bus_wdata}    ),
    .data_be_i        ( {s_mperiph_bus_be,          s_core_periph_bus_be}       ),
    .data_gnt_o       ( {s_mperiph_bus_gnt,         s_core_periph_bus_gnt}      ),
    .data_r_valid_o   ( {s_mperiph_bus_r_valid,     s_core_periph_bus_r_valid}  ),
    .data_r_rdata_o   ( {s_mperiph_bus_r_rdata,     s_core_periph_bus_r_rdata}  ),
    .data_r_opc_o     ( {s_mperiph_bus_r_opc,       s_core_periph_bus_r_opc}    ),
    .data_req_o       ( s_speriph_bus_req                                       ),
    .data_add_o       ( s_speriph_bus_add                                       ),
    .data_wen_o       ( s_speriph_bus_wen                                       ),
    .data_atop_o      ( s_speriph_bus_atop                                      ),
    .data_wdata_o     ( s_speriph_bus_wdata                                     ),
    .data_be_o        ( s_speriph_bus_be                                        ),
    .data_ID_o        ( s_speriph_bus_id                                        ),
    .data_gnt_i       ( s_speriph_bus_gnt                                       ),
    .data_r_rdata_i   ( s_speriph_bus_r_rdata                                   ),
    .data_r_valid_i   ( s_speriph_bus_r_valid                                   ),
    .data_r_ID_i      ( s_speriph_bus_r_id                                      ),
    .data_r_opc_i     ( s_speriph_bus_r_opc                                     )
  );

endmodule
