///! # Snitch Cluster configuration.
///! This needs to be adapted for each new chip/system.
package snitch_cfg;

  localparam int NumFPOutstandingLoads = 4;
  localparam int NumIntOutstandingLoads = 1;
  // Number of instructions the sequencer can hold
  localparam int FPUSequencerInstr = 16;
  // SSRs
  localparam snitch_pkg::addr_t SSR_ADDR_BASE = 32'h20_4800;
  localparam snitch_pkg::addr_t SSR_ADDR_MASK = 32'hffff_fe00;
  localparam logic [11:0] CSR_SSR = 12'h7C0;
  localparam int SSRNrCredits = 4;
  localparam logic [11:0] CSR_MSEG = 12'hBC0;

  // ------------------
  // FPU Configuration
  // ------------------

  // Latencies of FP ops (number of regs)
  localparam int unsigned LAT_COMP_FP32    = 'd3;
  localparam int unsigned LAT_COMP_FP64    = 'd3;
  localparam int unsigned LAT_COMP_FP16    = 'd2;
  localparam int unsigned LAT_COMP_FP16ALT = 'd2;
  localparam int unsigned LAT_COMP_FP8     = 'd1;
  localparam int unsigned LAT_DIVSQRT      = 'd1;
  localparam int unsigned LAT_NONCOMP      = 'd1;
  localparam int unsigned LAT_CONV         = 'd2;

  localparam fpnew_pkg::fpu_implementation_t FPU_IMPLEMENTATION = '{
    PipeRegs:  '{// FP32, FP64, FP16, FP8, FP16alt
                 '{LAT_COMP_FP32, LAT_COMP_FP64, LAT_COMP_FP16, LAT_COMP_FP8, LAT_COMP_FP16ALT}, // ADDMUL
                 '{default: LAT_DIVSQRT}, // DIVSQRT
                 '{default: LAT_NONCOMP}, // NONCOMP
                 '{default: LAT_CONV}},   // CONV
    UnitTypes: '{'{default: fpnew_pkg::MERGED},
                 // '{fpnew_pkg::PARALLEL, fpnew_pkg::PARALLEL, fpnew_pkg::MERGED, fpnew_pkg::MERGED, fpnew_pkg::MERGED}, // ADDMUL
                 '{default: fpnew_pkg::DISABLED}, // DIVSQRT
                 '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                 '{default: fpnew_pkg::MERGED}},  // CONV
    PipeConfig: fpnew_pkg::BEFORE
    // PipeConfig: fpnew_pkg::DISTRIBUTED
  };

  // Amount of address bit which should be used for accesses from the SoC side.
  // This effectively determines the Address Space of a Snitch Cluster.
  localparam SoCRequestAddrBits = 32;

  // Address Map
  // TCDM, everything below 0x4000_0000
  localparam snitch_pkg::addr_t TCDMStartAddress = 'h0000_0000;
  localparam snitch_pkg::addr_t TCDMMask         = '1 << 28;

  localparam logic [31:0] ClusterPeriphStartAddress = 'h4000_0000;


  localparam int unsigned NrRules = snitch_pkg::NrSlaves;

  localparam axi_pkg::xbar_cfg_t CLUSTER_XBAR_CFG = '{
    NoSlvPorts: snitch_pkg::NrMasters,
    NoMstPorts: snitch_pkg::NrSlaves,
    MaxMstTrans: 4,
    MaxSlvTrans: 4,
    FallThrough: 1'b0,
    LatencyMode: axi_pkg::CUT_MST_PORTS,
    AxiIdWidthSlvPorts: snitch_pkg::IdWidth,
    AxiIdUsedSlvPorts: snitch_pkg::IdWidth,
    AxiAddrWidth: snitch_axi_pkg::AddrWidth,
    AxiDataWidth: snitch_axi_pkg::DataWidth,
    NoAddrRules: NrRules
  };

  localparam axi_pkg::xbar_rule_64_t [NrRules-1:0] CLUSTER_XBAR_RULES = '{
    '{idx: snitch_pkg::TCDM,               start_addr: TCDMStartAddress,          end_addr: TCDMStartAddress + 'h1000_0000},
    '{idx: snitch_pkg::ClusterPeripherals, start_addr: ClusterPeriphStartAddress, end_addr: 'h5000_0000},
    '{idx: snitch_pkg::SoC,                start_addr: 'h8000_0000,               end_addr: '1}
  };

  // DMA configuration struct
  localparam axi_pkg::xbar_cfg_t dma_xbar_cfg = '{
    NoSlvPorts:          snitch_pkg::NrDmaMasters,
    NoMstPorts:          snitch_pkg::NrDmaSlaves,
    MaxMstTrans:         4,
    MaxSlvTrans:         4,
    FallThrough:         1'b0,
    LatencyMode:         axi_pkg::CUT_ALL_PORTS,
    AxiIdWidthSlvPorts:  snitch_pkg::IdWidthDma,
    AxiIdUsedSlvPorts:   snitch_pkg::IdWidthDma,
    AxiAddrWidth:        snitch_axi_pkg::DMAAddrWidth,
    AxiDataWidth:        snitch_axi_pkg::DMADataWidth,
    NoAddrRules:         2
  };

  localparam axi_pkg::xbar_rule_64_t [dma_xbar_cfg.NoAddrRules-1:0] dma_xbar_rule = '{
    '{idx: snitch_pkg::SoCDMA,  start_addr: TCDMStartAddress + 64'h0000_0000_1000_0000, end_addr: 64'hFFFF_FFFF_FFFF_FFFF                    },
    '{idx: snitch_pkg::TCDMDMA, start_addr: TCDMStartAddress,                           end_addr: TCDMStartAddress + 64'h0000_0000_1000_0000 }
  };

  localparam snitch_pma_pkg::snitch_pma_t DefaultSnitchCfg = '{
    NrNonIdempotentRegionRules: 0,
    NonIdempotentRegion: '{
      '{base: 32'h0, mask: 32'h0}
    },
    NrExecuteRegionRules: 0,
    ExecuteRegion: '{
      '{base: 32'h0, mask: 32'h0}
    },
    NrCachedRegionRules: 1,
    CachedRegion: '{
      // The upper half of the address space is cashable
      '{base: 32'h8000_0000, mask: 32'h8000_0000}
    },
    NrAMORegionRules: 0,
    AMORegion: '{
      '{base: 32'h0, mask: 32'h0}
    }
  };

endpackage