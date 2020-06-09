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
  parameter NB_HWPE_PORTS   = 4,
  parameter bit HWPE_PRESENT = 1'b1,
  parameter NB_DMAS         = 4,
  parameter NB_EXT          = 4,
  parameter NB_MPERIPHS     = 1,
  parameter NB_TCDM_BANKS   = 16,
  parameter NB_SPERIPHS     = 8,
  parameter DATA_WIDTH      = 32,
  parameter ADDR_WIDTH      = 32,
  parameter BE_WIDTH        = DATA_WIDTH/8,
  //TCDM PARAMETERS
  parameter TEST_SET_BIT    = 20,
  parameter ADDR_MEM_WIDTH  = 11,
  parameter LOG_CLUSTER     = 5,
  parameter PE_ROUTING_LSB  = 16,
  parameter PE_ROUTING_MSB  = 19,
  parameter ADDREXT         = 1'b0,
  parameter CLUSTER_ALIAS      = 1'b0,
  parameter CLUSTER_ALIAS_BASE = 12'h000
)
(
  input logic                          clk_i,
  input logic                          rst_ni,
  XBAR_TCDM_BUS.Slave                  core_tcdm_slave[NB_CORES+NB_HWPE_PORTS-1:0],
  input logic [NB_CORES-1:0][5:0]      core_tcdm_slave_atop,
  XBAR_PERIPH_BUS.Slave                core_periph_slave[NB_CORES-1:0],
  input logic [NB_CORES-1:0][5:0]      core_periph_slave_atop,
  input logic [NB_CORES-1:0][31:0]     core_periph_slave_addrext,
  XBAR_TCDM_BUS.Slave                  ext_slave[NB_EXT-1:0],
  input logic [NB_EXT-1:0][5:0]        ext_slave_atop,
  XBAR_TCDM_BUS.Slave                  dma_slave[NB_DMAS-1:0],
  XBAR_TCDM_BUS.Slave                  mperiph_slave[NB_MPERIPHS-1:0],
  TCDM_BANK_MEM_BUS.Master             tcdm_sram_master[NB_TCDM_BANKS-1:0],
  XBAR_PERIPH_BUS.Master               speriph_master[NB_SPERIPHS-1:0],
  output logic [NB_SPERIPHS-1:0][5:0]  speriph_master_atop,
  input logic [1:0]                    TCDM_arb_policy_i
);

  localparam TCDM_ID_WIDTH = NB_CORES+NB_DMAS+NB_EXT+NB_HWPE_PORTS;

  // DMA --> LOGARITHMIC INTERCONNECT BUS SIGNALS
  logic [NB_EXT+NB_DMAS-1:0][DATA_WIDTH-1:0] s_dma_bus_wdata;
  logic [NB_EXT+NB_DMAS-1:0][ADDR_WIDTH-1:0] s_dma_bus_add;
  logic [NB_EXT+NB_DMAS-1:0]                 s_dma_bus_req;
  logic [NB_EXT+NB_DMAS-1:0]                 s_dma_bus_wen;
  logic [NB_EXT+NB_DMAS-1:0][BE_WIDTH-1:0]   s_dma_bus_be;
  logic [NB_EXT+NB_DMAS-1:0]                 s_dma_bus_gnt;
  logic [NB_EXT+NB_DMAS-1:0][DATA_WIDTH-1:0] s_dma_bus_r_rdata;
  logic [NB_EXT+NB_DMAS-1:0]                 s_dma_bus_r_valid;

  // DEMUX --> LOGARITHMIC INTERCONNECT BUS SIGNALS
  logic [NB_CORES+NB_HWPE_PORTS-1:0][DATA_WIDTH-1:0] s_core_tcdm_bus_wdata;
  logic [NB_CORES+NB_HWPE_PORTS-1:0][ADDR_WIDTH-1:0] s_core_tcdm_bus_add;
  logic [NB_CORES+NB_HWPE_PORTS-1:0]                 s_core_tcdm_bus_req;
  logic [NB_CORES+NB_HWPE_PORTS-1:0]                 s_core_tcdm_bus_wen;
  logic [NB_CORES+NB_HWPE_PORTS-1:0][BE_WIDTH-1:0]   s_core_tcdm_bus_be;
  logic [NB_CORES+NB_HWPE_PORTS-1:0]                 s_core_tcdm_bus_gnt;
  logic [NB_CORES+NB_HWPE_PORTS-1:0][DATA_WIDTH-1:0] s_core_tcdm_bus_r_rdata;
  logic [NB_CORES+NB_HWPE_PORTS-1:0]                 s_core_tcdm_bus_r_valid;

  // LOGARITHMIC INTERCONNECT --> AMO Shims
  logic [NB_TCDM_BANKS-1:0][ADDR_MEM_WIDTH-1:0] s_tcdm_bus_amo_shim_add;
  logic [NB_TCDM_BANKS-1:0]                     s_tcdm_bus_amo_shim_req;
  logic [NB_TCDM_BANKS-1:0]                     s_tcdm_bus_amo_shim_gnt;
  logic [NB_TCDM_BANKS-1:0]                     s_tcdm_bus_amo_shim_wen;
  logic [NB_TCDM_BANKS-1:0][BE_WIDTH-1:0]       s_tcdm_bus_amo_shim_be;

  generate
    for (genvar i=0; i<NB_CORES+NB_HWPE_PORTS; i++) begin : CORE_TCDM_BIND
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
    for (genvar i=0; i<NB_EXT; i++) begin : AXI2MEM_BIND
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
      assign s_dma_bus_add[NB_EXT+i]    = dma_slave[i].add;
      assign s_dma_bus_req[NB_EXT+i]    = dma_slave[i].req;
      assign s_dma_bus_wdata[NB_EXT+i]  = dma_slave[i].wdata;
      assign s_dma_bus_wen[NB_EXT+i]    = dma_slave[i].wen;
      assign s_dma_bus_be[NB_EXT+i]     = dma_slave[i].be;

      assign dma_slave[i].gnt      = s_dma_bus_gnt[NB_EXT+i];
      assign dma_slave[i].r_valid  = s_dma_bus_r_valid[NB_EXT+i];
      assign dma_slave[i].r_rdata  = s_dma_bus_r_rdata[NB_EXT+i];
    end
  endgenerate

  localparam NUM_TCDM_ICONN_IN = NB_CORES + NB_HWPE_PORTS + NB_DMAS + NB_EXT;
  typedef struct packed {
    logic [DATA_WIDTH-1:0]  data;
    logic [5:0]             atop;
  } tcdm_data_t;
  tcdm_data_t [NUM_TCDM_ICONN_IN-1:0] iconn_inp_wdata, iconn_inp_rdata;
  tcdm_data_t     [NB_TCDM_BANKS-1:0] iconn_oup_wdata, iconn_oup_rdata;
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
    if (i < NB_CORES + NB_HWPE_PORTS) begin
      assign iconn_inp_wdata[i].data = s_core_tcdm_bus_wdata[i];
      assign s_core_tcdm_bus_r_rdata[i] = iconn_inp_rdata[i].data;
    end else begin
      assign iconn_inp_wdata[i].data = s_dma_bus_wdata[i - (NB_CORES + NB_HWPE_PORTS)];
      assign s_dma_bus_r_rdata[i - (NB_CORES + NB_HWPE_PORTS)] = iconn_inp_rdata[i].data;
    end
    if (i < NB_CORES) begin
      assign iconn_inp_wdata[i].atop = core_tcdm_slave_atop[i];
    end else if (i < NB_CORES + NB_EXT) begin
      assign iconn_inp_wdata[i].atop = ext_slave_atop[i-NB_CORES];
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
      amo = '0;
      data = iconn_oup_wdata[i].data;
      if (atop[5]) begin
        unique casez (atop[4:0])
          riscv_defines::AMO_ADD:   amo = 4'h2;
          riscv_defines::AMO_SWAP:  amo = 4'h1;
          riscv_defines::AMO_LR:    `ifndef TARGET_SYNTHESIS $error("Unsupported LR on L1!") `endif;
          riscv_defines::AMO_SC:    `ifndef TARGET_SYNTHESIS $error("Unsupported SC on L1!") `endif;
          default: begin
            `ifndef TARGET_SYNTHESIS
              assert (atop[1:0] == '0) else $error("Illegal AMO!");
            `endif
            unique case (atop[4:2])
              riscv_defines::AMO_XOR[4:2]:  amo = 4'h5;
              riscv_defines::AMO_OR[4:2]:   amo = 4'h4;
              riscv_defines::AMO_AND[4:2]:  amo = 4'h3;
              riscv_defines::AMO_MIN[4:2]:  amo = 4'h8;
              riscv_defines::AMO_MAX[4:2]:  amo = 4'h6;
              riscv_defines::AMO_MINU[4:2]: amo = 4'h9;
              riscv_defines::AMO_MAXU[4:2]: amo = 4'h7;
              default:                      amo = 4'h0;
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

  localparam int unsigned PE_XBAR_N_INPS = NB_CORES + NB_MPERIPHS;
  localparam int unsigned PE_XBAR_N_OUPS = NB_SPERIPHS;
  typedef logic [ADDR_WIDTH-1:0]              pe_addr_t;
  typedef logic [DATA_WIDTH-1:0]              pe_data_t;
  typedef logic [$clog2(PE_XBAR_N_OUPS)-1:0]  pe_idx_t;
  typedef logic [PE_XBAR_N_INPS-1:0]          pe_id_t;
  typedef struct packed {
    pe_addr_t             addr;
    pe_data_t             data;
    pe_id_t               id;
    logic                 we_n; // active low on `XBAR_PERIPH_BUS` and `XBAR_TCDM_BUS`
    logic [BE_WIDTH-1:0]  be;
    logic          [5:0]  atop;
  } pe_req_t;
  typedef struct packed {
    pe_data_t   data;
    pe_id_t     id;
    logic       opc;
  } pe_resp_t;

  // Peripherals: Bind inputs and decode addresses.
  pe_idx_t  [PE_XBAR_N_INPS-1:0]  pe_inp_idx;
  pe_req_t  [PE_XBAR_N_INPS-1:0]  pe_inp_wdata;
  pe_resp_t [PE_XBAR_N_INPS-1:0]  pe_inp_rdata;
  logic     [PE_XBAR_N_INPS-1:0]  pe_inp_req,
                                  pe_inp_gnt,
                                  pe_inp_rvalid;
  localparam pe_idx_t PE_IDX_EXT = pulp_cluster_package::SPER_EXT_ID;
  localparam pe_idx_t PE_IDX_ERR = pulp_cluster_package::SPER_ERROR_ID;
  function automatic pe_idx_t addr_to_pe_idx(input pe_addr_t addr, input logic [31:0] addrext);
    pe_idx_t pe_idx;
    if (ADDREXT && addrext != '0) begin
      return PE_IDX_EXT;
    end else begin
      if (
        // if the access is to this cluster ..
        (addr[31:24] == 8'h10 || (CLUSTER_ALIAS && addr[31:24] == CLUSTER_ALIAS_BASE[11:4]))
        // .. and the peripherals
        && (addr[23:20] >= 4'h2 && addr[23:20] <= 4'h3)
      ) begin
        // decode peripheral to access
        pe_idx = addr[PE_ROUTING_MSB:PE_ROUTING_LSB];
        if (addr[23:20] == 4'h2 && addr[19:PE_ROUTING_MSB+1] == '0 && pe_idx < NB_SPERIPHS) begin
          if (pe_idx >= pulp_cluster_package::SPER_EVENT_U_ID &&
              pe_idx < pulp_cluster_package::SPER_EVENT_U_ID
                        + pulp_cluster_package::NB_SPERIPH_PLUGS_EU
          ) begin
            // Index is in event unit range, so return unified event unit port.
            return pulp_cluster_package::SPER_EVENT_U_ID;
          end else if (!HWPE_PRESENT && pe_idx == pulp_cluster_package::SPER_HWPE_ID) begin
            // Decode non-present HWPE to error slave.
            return PE_IDX_ERR;
          end else if (pe_idx == PE_IDX_EXT) begin
            // Decode direct accesses to external peripheral to error slave to break addressing
            // loop.
            return PE_IDX_ERR;
          end else begin
            // Return index of other peripheral.
            return pe_idx;
          end
        // .. or, if the address does not decode to a peripheral, decode to error slave
        end else begin
          return PE_IDX_ERR;
        end
      end else begin
        // otherwise decode to 'external' peripheral
        return PE_IDX_EXT;
      end
    end
  endfunction
  for (genvar i = 0; i < NB_CORES; i++) begin : gen_pe_xbar_bind_cores
    assign pe_inp_req[i] = core_periph_slave[i].req;
    assign pe_inp_idx[i] = addr_to_pe_idx(core_periph_slave[i].add, core_periph_slave_addrext[i]);
    assign pe_inp_wdata[i].addr = core_periph_slave[i].add;
    assign pe_inp_wdata[i].data = core_periph_slave[i].wdata;
    assign pe_inp_wdata[i].id   = 1 << i;
    assign pe_inp_wdata[i].we_n = core_periph_slave[i].wen;
    assign pe_inp_wdata[i].be   = core_periph_slave[i].be;
    assign pe_inp_wdata[i].atop = core_periph_slave_atop[i];
    assign core_periph_slave[i].gnt     = pe_inp_gnt[i];
    assign core_periph_slave[i].r_id    = pe_inp_rdata[i].id;
    assign core_periph_slave[i].r_rdata = pe_inp_rdata[i].data;
    assign core_periph_slave[i].r_opc   = pe_inp_rdata[i].opc;
    assign core_periph_slave[i].r_valid = pe_inp_rvalid[i];
  end
  for (genvar i = 0; i < NB_MPERIPHS; i++) begin : gen_pe_xbar_bind_mperiphs
    assign pe_inp_req[i+NB_CORES] = mperiph_slave[i].req;
    assign pe_inp_idx[i+NB_CORES] = addr_to_pe_idx(mperiph_slave[i].add, '0);
    assign pe_inp_wdata[i+NB_CORES].addr  = mperiph_slave[i].add;
    assign pe_inp_wdata[i+NB_CORES].data  = mperiph_slave[i].wdata;
    assign pe_inp_wdata[i+NB_CORES].id    = 1 << (i + NB_CORES);
    assign pe_inp_wdata[i+NB_CORES].we_n  = mperiph_slave[i].wen;
    assign pe_inp_wdata[i+NB_CORES].be    = mperiph_slave[i].be;
    assign pe_inp_wdata[i+NB_CORES].atop  = '0;
    assign mperiph_slave[i].gnt     = pe_inp_gnt[i+NB_CORES];
    assign mperiph_slave[i].r_rdata = pe_inp_rdata[i+NB_CORES].data;
    assign mperiph_slave[i].r_opc   = pe_inp_rdata[i+NB_CORES].opc;
    assign mperiph_slave[i].r_valid = pe_inp_rvalid[i+NB_CORES];
  end

  // Peripherals: Bind outputs.
  pe_req_t  [PE_XBAR_N_OUPS-1:0]  pe_oup_wdata;
  pe_resp_t [PE_XBAR_N_OUPS-1:0]  pe_oup_rdata;
  logic     [PE_XBAR_N_OUPS-1:0]  pe_oup_req,
                                  pe_oup_gnt,
                                  pe_oup_rvalid;
  for (genvar i = 0; i < NB_SPERIPHS; i++) begin : gen_pe_xbar_bind_speriphs
    assign speriph_master[i].req    = pe_oup_req[i];
    assign pe_oup_gnt[i]            = speriph_master[i].gnt;
    assign speriph_master[i].add    = pe_oup_wdata[i].addr;
    assign speriph_master[i].wdata  = pe_oup_wdata[i].data;
    assign speriph_master[i].id     = pe_oup_wdata[i].id;
    assign speriph_master[i].wen    = pe_oup_wdata[i].we_n;
    assign speriph_master[i].be     = pe_oup_wdata[i].be;
    assign speriph_master_atop[i]   = pe_oup_wdata[i].atop;
    assign pe_oup_rdata[i].data = speriph_master[i].r_rdata;
    assign pe_oup_rdata[i].id   = speriph_master[i].r_id;
    assign pe_oup_rdata[i].opc  = speriph_master[i].r_opc;
    assign pe_oup_rvalid[i] = speriph_master[i].r_valid;
  end

  // Peripheral Interconnect
  logic [PE_XBAR_N_INPS-1:0][PE_XBAR_N_OUPS-1:0] pe_req, pe_gnt;
  // Demux requests of inputs and mux responses to inputs.
  for (genvar i = 0; i < PE_XBAR_N_INPS; i++) begin : gen_pe_xbar_inps
    stream_demux #(
      .N_OUP(PE_XBAR_N_OUPS)
    ) i_req_demux (
      .inp_valid_i  (pe_inp_req[i]),
      .inp_ready_o  (pe_inp_gnt[i]),
      .oup_sel_i    (pe_inp_idx[i]),
      .oup_valid_o  (pe_req[i]),
      .oup_ready_i  (pe_gnt[i])
    );
    logic [PE_XBAR_N_OUPS-1:0] pe_oup_reqs;
    for (genvar j = 0; j < PE_XBAR_N_OUPS; j++) begin : gen_pe_xbar_inps_oup_reqs
      assign pe_oup_reqs[j] = pe_oup_rvalid[j] & (pe_oup_rdata[j].id == 1 << i);
    end
    pe_idx_t oup_sel;
    onehot_to_bin #(
      .ONEHOT_WIDTH (PE_XBAR_N_OUPS)
    ) i_ohb (
      .onehot (pe_oup_reqs),
      .bin    (oup_sel)
    );
    stream_mux #(
      .DATA_T (pe_resp_t),
      .N_INP  (PE_XBAR_N_OUPS)
    ) i_resp_mux (
      .inp_data_i   (pe_oup_rdata),
      .inp_valid_i  (pe_oup_reqs),
      .inp_ready_o  (/* unused */),
      .inp_sel_i    (oup_sel),
      .oup_data_o   (pe_inp_rdata[i]),
      .oup_valid_o  (pe_inp_rvalid[i]),
      .oup_ready_i  (1'b1)
    );
  end
  // Arbitrate requests to outputs.
  for (genvar i = 0; i < PE_XBAR_N_OUPS; i++) begin : gen_pe_xbar_oups
    logic [PE_XBAR_N_INPS-1:0] reqs, gnts;
    for (genvar j = 0; j < PE_XBAR_N_INPS; j++) begin : gen_pe_xbar_oup_arb_inps
      assign reqs[j] = pe_req[j][i];
      assign pe_gnt[j][i] = gnts[j];
    end
    rr_arb_tree #(
      .NumIn      (PE_XBAR_N_INPS),
      .DataWidth  ($bits(pe_req_t)),
      .ExtPrio    (1'b0),
      .AxiVldRdy  (1'b0),
      .LockIn     (1'b0)
    ) i_arb (
      .clk_i,
      .rst_ni,
      .flush_i  (1'b0),
      .rr_i     ('0),

      .req_i    (reqs),
      .gnt_o    (gnts),
      .data_i   (pe_inp_wdata),

      .gnt_i    (pe_oup_gnt[i]),
      .req_o    (pe_oup_req[i]),
      .data_o   (pe_oup_wdata[i]),
      .idx_o    (/* unused */)
    );
  end

endmodule
