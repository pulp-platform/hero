// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Wolfgang Rönninger <wroennin@iis.ee.ethz.ch>

/// AXI4+ATOP to banked SRAM memory slave. Allows for parallel read and write transactions.
module axi_to_mem_banked #(
  /// AXI4+ATOP ID width
  parameter int unsigned                  AxiIdWidth    = 32'd0,
  /// AXI4+ATOP address width
  parameter int unsigned                  AxiAddrWidth  = 32'd0,
  /// AXI4+ATOP data width
  parameter int unsigned                  AxiDataWidth  = 32'd0,
  /// AXI4+ATOP AW channel struct
  parameter type                          axi_aw_chan_t = logic,
  /// AXI4+ATOP  W channel struct
  parameter type                          axi_w_chan_t  = logic,
  /// AXI4+ATOP  B channel struct
  parameter type                          axi_b_chan_t  = logic,
  /// AXI4+ATOP AR channel struct
  parameter type                          axi_ar_chan_t = logic,
  /// AXI4+ATOP  R channel struct
  parameter type                          axi_r_chan_t  = logic,
  /// AXI4+ATOP request struct
  parameter type                          axi_req_t     = logic,
  /// AXI4+ATOP response struct
  parameter type                          axi_resp_t    = logic,
  /// Number of memory banks / macros
  /// Has to satisfy:
  /// - MemNumBanks >= 2 * AxiDataWidth / MemDataWidth
  /// - MemNumBanks is a power of 2.
  parameter int unsigned                  MemNumBanks   = 32'd4,
  /// Address width of an individual memory bank.
  parameter int unsigned                  MemAddrWidth  = 32'd11,
  /// Data width of the memory macros.
  /// Has to satisfy:
  /// - AxiDataWidth % MemDataWidth = 0
  parameter int unsigned                  MemDataWidth  = 32'd32,
  /// Read latency of the connected memory in cycles
  parameter int unsigned                  MemLatency    = 32'd1,
  /// TCDM topology can be: LIC, BFLY2, BFLY4, CLOS
  parameter tcdm_interconnect_pkg::topo_e Topology      = tcdm_interconnect_pkg::LIC,
  /// DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter type mem_addr_t = logic [MemAddrWidth-1:0],
  parameter type mem_atop_t = logic [5:0],
  parameter type mem_data_t = logic [MemDataWidth-1:0],
  parameter type mem_strb_t = logic [MemDataWidth/8-1:0]
) (
  /// Clock
  input  logic                        clk_i,
  /// Asynchronous reset, active low
  input  logic                        rst_ni,
  /// Testmode enable
  input  logic                        test_i,
  /// AXI4+ATOP slave port, request struct
  input  axi_req_t                    axi_req_i,
  /// AXI4+ATOP slave port, response struct
  output axi_resp_t                   axi_resp_o,
  /// Memory bank request
  output logic      [MemNumBanks-1:0] mem_req_o,
  /// Memory request grant
  input  logic      [MemNumBanks-1:0] mem_gnt_i,
  /// Request address
  output mem_addr_t [MemNumBanks-1:0] mem_add_o,
  /// Write request enable, active high
  output logic      [MemNumBanks-1:0] mem_wen_o,
  /// Write data
  output mem_data_t [MemNumBanks-1:0] mem_wdata_o,
  /// Write data byte enable, active high
  output mem_strb_t [MemNumBanks-1:0] mem_be_o,
  /// Atomic operation
  output mem_atop_t [MemNumBanks-1:0] mem_atop_o,
  /// Read data response
  input  mem_data_t [MemNumBanks-1:0] mem_rdata_i,
  /// Status output, busy flag of `axi_to_mem`
  output logic      [1:0]             axi_to_mem_busy_o
);
  localparam int unsigned BanksPerAxiChannel = AxiDataWidth / MemDataWidth;
  // atop signal is piggybacked on tcdm_data
  localparam int unsigned TcdmDataWidth = MemDataWidth + 6;

  // Typedef for defining the channels
  typedef enum logic {
    ReadAccess  = 1'b0,
    WriteAccess = 1'b1
  } access_type_e;
  typedef logic [AxiAddrWidth-1:0]   axi_addr_t;
  typedef logic [TcdmDataWidth-1:0] tcdm_data_t;

  axi_req_t  [1:0] mem_axi_reqs;
  axi_resp_t [1:0] mem_axi_resps;

  // Fixed select `axi_demux` to split reads and writes to the two `axi_to_mem`
  axi_demux #(
    .AxiIdWidth  ( AxiIdWidth    ),
    .aw_chan_t   ( axi_aw_chan_t ),
    .w_chan_t    ( axi_w_chan_t  ),
    .b_chan_t    ( axi_b_chan_t  ),
    .ar_chan_t   ( axi_ar_chan_t ),
    .r_chan_t    ( axi_r_chan_t  ),
    .req_t       ( axi_req_t     ),
    .resp_t      ( axi_resp_t    ),
    .NoMstPorts  ( 32'd2         ),
    .MaxTrans    ( 32'd4         ), // allow multiple Ax vectors to not starve W channel
    .AxiLookBits ( 32'd1         ), // select is fixed, do not need it
    .FallThrough ( 1'b1          ),
    .SpillAw     ( 1'b1          ),
    .SpillW      ( 1'b1          ),
    .SpillB      ( 1'b1          ),
    .SpillAr     ( 1'b1          ),
    .SpillR      ( 1'b1          )
  ) i_axi_demux (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_req_i       ( axi_req_i     ),
    .slv_aw_select_i ( WriteAccess   ),
    .slv_ar_select_i ( ReadAccess    ),
    .slv_resp_o      ( axi_resp_o    ),
    .mst_reqs_o      ( mem_axi_reqs  ),
    .mst_resps_i     ( mem_axi_resps )
  );

  logic       [1:0][BanksPerAxiChannel-1:0] inter_req;
  logic       [1:0][BanksPerAxiChannel-1:0] inter_gnt;
  axi_addr_t  [1:0][BanksPerAxiChannel-1:0] inter_addr;
  tcdm_data_t [1:0][BanksPerAxiChannel-1:0] inter_wdata;
  mem_strb_t  [1:0][BanksPerAxiChannel-1:0] inter_strb;
  logic       [1:0][BanksPerAxiChannel-1:0] inter_we;
  logic       [1:0][BanksPerAxiChannel-1:0] inter_rvalid;
  tcdm_data_t [1:0][BanksPerAxiChannel-1:0] inter_rdata;
  // axi_to_mem protocol converter
  for (genvar i = 0; i < 2; i++) begin : gen_axi_to_mem
    mem_data_t [BanksPerAxiChannel-1:0] wdata, rdata;
    mem_atop_t [BanksPerAxiChannel-1:0] atop;
    axi_to_mem #(
      .axi_req_t ( axi_req_t          ),
      .axi_resp_t( axi_resp_t         ),
      .AddrWidth ( AxiAddrWidth       ),
      .DataWidth ( AxiDataWidth       ),
      .IdWidth   ( AxiIdWidth         ),
      .NumBanks  ( BanksPerAxiChannel ),
      .BufDepth  ( MemLatency         )
    ) i_axi_to_mem (
      .clk_i,
      .rst_ni,
      .busy_o       ( axi_to_mem_busy_o[i] ),
      .axi_req_i    ( mem_axi_reqs[i]      ),
      .axi_resp_o   ( mem_axi_resps[i]     ),
      .mem_req_o    ( inter_req[i]         ),
      .mem_gnt_i    ( inter_gnt[i]         ),
      .mem_addr_o   ( inter_addr[i]        ),
      .mem_wdata_o  ( wdata                ),
      .mem_strb_o   ( inter_strb[i]        ),
      .mem_atop_o   ( atop                 ),
      .mem_we_o     ( inter_we[i]          ),
      .mem_rvalid_i ( inter_rvalid[i]      ),
      .mem_rdata_i  ( rdata                )
    );
    // atomic data is feed through the TCDM together with the write data
    for (genvar j = 0; j < BanksPerAxiChannel; j++) begin
      assign inter_wdata[i][j] = {atop[j], wdata[j]};
      // discard the padding zeros (atop) on the response data
      assign rdata[j]          = mem_data_t'(inter_rdata[i][j]);
    end
  end

  tcdm_data_t [MemNumBanks-1:0] tcdm_wdata, tcdm_rdata;
  tcdm_interconnect #(
    .NumIn        ( 2 * BanksPerAxiChannel   ),
    .NumOut       ( MemNumBanks              ),
    .AddrWidth    ( AxiAddrWidth             ),
    .DataWidth    ( TcdmDataWidth            ),
    .BeWidth      ( MemDataWidth / 8         ),
    .AddrMemWidth ( MemAddrWidth             ),
    .ByteOffWidth ( $clog2(MemDataWidth-1)-3 ), // explicit offset as atop is in data
    .WriteRespOn  ( 1'b1                     ), // `axi_to_mem` expects a write response
    .RespLat      ( MemLatency               ),
    .Topology     ( Topology                 ),
    .NumPar       ( 1                        )
  ) i_tcdm_interconnect (
    .clk_i,
    .rst_ni,
    .req_i   ( inter_req    ),
    .add_i   ( inter_addr   ),
    .wen_i   ( inter_we     ),
    .wdata_i ( inter_wdata  ),
    .be_i    ( inter_strb   ),
    .gnt_o   ( inter_gnt    ),
    .vld_o   ( inter_rvalid ),
    .rdata_o ( inter_rdata  ),
    .req_o   ( mem_req_o    ),
    .gnt_i   ( mem_gnt_i    ),
    .add_o   ( mem_add_o    ),
    .wen_o   ( mem_wen_o    ),
    .wdata_o ( tcdm_wdata   ),
    .be_o    ( mem_be_o     ),
    .rdata_i ( tcdm_rdata   )
  );
  for (genvar i = 0; i < MemNumBanks; i++) begin : gen_deaggregate_data
    assign {mem_atop_o[i], mem_wdata_o[i]} = tcdm_wdata[i];
    // response data appended with zeros as there is no atomic on the return path
    assign tcdm_rdata[i]                   = {6'b0, mem_rdata_i[i]};
  end

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AxiIdWidth   >= 1) else $fatal(1, "AxiIdWidth must be at least 1!");
    assert (AxiAddrWidth >= 1) else $fatal(1, "AxiAddrWidth must be at least 1!");
    assert (AxiDataWidth >= 1) else $fatal(1, "AxiDataWidth must be at least 1!");
    assert (MemNumBanks  >= 2 * AxiDataWidth / MemDataWidth) else
        $fatal(1, "MemNumBanks has to be >= 2 * AxiDataWidth / MemDataWidth");
    assert ($onehot(MemNumBanks)) else $fatal(1, "MemNumBanks has to be a power of 2.");
    assert (MemAddrWidth >= 1) else $fatal(1, "MemAddrWidth must be at least 1!");
    assert (MemDataWidth >= 1) else $fatal(1, "MemDataWidth must be at least 1!");
    assert (AxiDataWidth % MemDataWidth == 0) else
        $fatal(1, "MemDataWidth has to be a divisor of AxiDataWidth.");
  end
`endif
// pragma translate_on
endmodule
