///! # Snitch Constants.
///! Fixed constants for a Snitch system.
package snitch_pkg;

  localparam PLEN = 48;
  typedef logic [PLEN-1:0] addr_t;

  typedef struct packed {
    logic [63:0] BootAddress;
    int unsigned NrCores;
  } SnitchCfg;

  typedef struct packed {
    addr_t       addr;
    logic [3:0]  amo;
    logic        write;
    logic [63:0] data;
    logic [1:0]  size;
    logic [7:0]  strb;
  } dreq_t;

  typedef struct packed {
    logic [63:0] data;
    logic        error;
  } dresp_t;

  typedef struct packed {
    logic [31:0]   addr;
    logic [4:0]    id;
    logic [31:0]   data_op;
    logic [63:0]   data_arga;
    logic [63:0]   data_argb;
    logic [63:0]   data_argc;
  } acc_req_t;

  typedef struct packed {
    logic [4:0]    id;
    logic          error;
    logic [63:0]   data;
  } acc_resp_t;

  typedef struct packed {
    logic [31:0] addr;
    logic        write;
    logic [63:0] data;
    logic [7:0]  strb;
  } inst_req_t;

  typedef enum logic [1:0] {
    PrivLvlM = 2'b11,
    PrivLvlS = 2'b01,
    PrivLvlU = 2'b00
  } priv_lvl_t;

  // Extension state.
  typedef enum logic [1:0] {
    XOff = 2'b00,
    XInitial = 2'b01,
    XClean = 2'b10,
    XDirty = 2'b11
  } x_state_e;

  typedef struct packed {
    logic         sd;     // signal dirty - read-only - hardwired zero
    logic [7:0]   wpri3;  // writes preserved reads ignored
    logic         tsr;    // trap sret
    logic         tw;     // time wait
    logic         tvm;    // trap virtual memory
    logic         mxr;    // make executable readable
    logic         sum;    // permit supervisor user memory access
    logic         mprv;   // modify privilege - privilege level for ld/st
    x_state_e     xs;     // extension register - hardwired to zero
    x_state_e     fs;     // extension register - hardwired to zero for non FP and to Dirty for FP.
    priv_lvl_t    mpp;    // holds the previous privilege mode up to machine
    logic [1:0]   wpri2;  // writes preserved reads ignored
    logic         spp;    // holds the previous privilege mode up to supervisor
    logic         mpie;   // machine interrupts enable bit active prior to trap
    logic         wpri1;  // writes preserved reads ignored
    logic         spie;   // supervisor interrupts enable bit active prior to trap
    logic         upie;   // user interrupts enable bit active prior to trap - hardwired to zero
    logic         mie;    // machine interrupts enable
    logic         wpri0;  // writes preserved reads ignored
    logic         sie;    // supervisor interrupts enable
    logic         uie;    // user interrupts enable - hardwired to zero
  } status_rv32_t;

  localparam PAGE_SHIFT = 12;

  typedef struct packed {
    logic [31:20] ppn1;
    logic [19:10] ppn0;
    logic [9:8]   rsw;
    logic         d;
    logic         a;
    logic         g;
    logic         u;
    logic         x;
    logic         w;
    logic         r;
    logic         v;
  } pte_sv32_t;

  localparam logic [3:0] INSTR_ADDR_MISALIGNED = 0;
  localparam logic [3:0] INSTR_ACCESS_FAULT    = 1;
  localparam logic [3:0] ILLEGAL_INSTR         = 2;
  localparam logic [3:0] BREAKPOINT            = 3;
  localparam logic [3:0] LD_ADDR_MISALIGNED    = 4;
  localparam logic [3:0] LD_ACCESS_FAULT       = 5;
  localparam logic [3:0] ST_ADDR_MISALIGNED    = 6;
  localparam logic [3:0] ST_ACCESS_FAULT       = 7;
  localparam logic [3:0] ENV_CALL_UMODE        = 8;  // environment call from user mode
  localparam logic [3:0] ENV_CALL_SMODE        = 9;  // environment call from supervisor mode
  localparam logic [3:0] ENV_CALL_MMODE        = 11; // environment call from machine mode
  localparam logic [3:0] INSTR_PAGE_FAULT      = 12; // Instruction page fault
  localparam logic [3:0] LOAD_PAGE_FAULT       = 13; // Load page fault
  localparam logic [3:0] STORE_PAGE_FAULT      = 15; // Store page fault

  // Registers which are used as SSRs
  localparam [4:0] FT0 = 5'b0;
  localparam [4:0] FT1 = 5'b1;
  localparam [1:0][4:0] SSRRegs = {FT1, FT0};
  function automatic logic is_ssr(logic [4:0] register);
    unique case (register)
      FT0, FT1: return 1'b1;
      default : return 0;
    endcase
  endfunction

  // FPU
  // Floating-point extensions configuration
  localparam bit RVF = 1'b1; // Is F extension enabled - MUST BE 1 IF D ENABLED!
  localparam bit RVD = 1'b1; // Is D extension enabled

  // Transprecision floating-point extensions configuration
  localparam bit XF16    = 1'b0; // Is half-precision float extension (Xf16) enabled
  localparam bit XF16ALT = 1'b0; // Is alt. half-precision float extension (Xf16alt) enabled
  localparam bit XF8     = 1'b0; // Is quarter-precision float extension (Xf8) enabled
  localparam bit XFVEC   = 1'b1; // Is vectorial float SIMD extension (Xfvec) enabled
  // Non-standard extension present
  localparam bit NSX = XF16 | XF16ALT | XF8 | XFVEC;
  // ------------------
  // FPU Configuration
  // ------------------
  localparam bit FP_PRESENT = RVF | RVD | XF16 | XF16ALT | XF8;

  localparam FLEN = RVD     ? 64 : // D ext.
                    RVF     ? 32 : // F ext.
                    XF16    ? 16 : // Xf16 ext.
                    XF16ALT ? 16 : // Xf16alt ext.
                    XF8     ? 8 :  // Xf8 ext.
                    0;             // Unused in case of no FP

  localparam fpnew_pkg::fpu_features_t FPU_FEATURES = '{
    Width:         fpnew_pkg::maximum(FLEN, 32),
    EnableVectors: XFVEC,
    EnableNanBox:  1'b1,
    FpFmtMask:     {RVF, RVD, XF16, XF8, XF16ALT},
    IntFmtMask:    {XFVEC && XF8, XFVEC && (XF16 || XF16ALT), 1'b1, 1'b0}
  };

  // Slaves on Cluster AXI Bus
  typedef enum integer {
    TCDM               = 0,
    ClusterPeripherals = 1,
    SoC                = 2
  } cluster_slave_e;

  typedef enum integer {
    CoreReq = 0,
    ICache  = 1,
    AXISoC  = 2
  } cluster_master_e;

  // Slaves on Cluster DMA AXI Bus
  typedef enum int unsigned {
    TCDMDMA  = 32'd0,
    SoCDMA   = 32'd1
  } cluster_slave_dma_e;

  typedef enum int unsigned {
    SDMAMst  = 32'd0
  } cluster_master_dma_e;

  localparam int unsigned NrSlaves = 3;
  localparam int unsigned NrMasters = 3;

  localparam int IdWidth = 2;
  localparam int IdWidthSlave = $clog2(NrMasters) + IdWidth;

  // DMA X-BAR configuration
  localparam int unsigned NrDmaSlaves = 2;
  localparam int unsigned NrDmaMasters = 1;
  localparam int IdWidthDma = 6;
  localparam int IdWidthDmaSlave = $clog2(NrDmaMasters) + IdWidthDma;

  // configuration of the DMA
  localparam DmaDataWidth        = 512;
  localparam DmaAddrWidth        =  64; // not fully parametric !
  localparam DmaTracing          =   0;
  localparam AxiDmaTwodFifoDepth =   2; // expensive parameters
  localparam AxiDmaTfFifoDepth   =   2; // expensive parameters
  localparam AxiAxReqDepth       =   2; // expensive parameters

  // Cluster Peripheral Registers
  typedef enum logic [19:0] {
    TCDMStartAddressReg = 20'h0_0000,
    TCDMEndAddressReg   = 20'h0_0008,
    NrCoresReg          = 20'h0_0010,
    FetchEnableReg      = 20'h0_0018,
    ScratchReg          = 20'h0_0020,
    WakeUpReg           = 20'h0_0028,
    CycleCountReg       = 20'h0_0030,
    BarrierReg          = 20'h0_0038,
    ClusterIdReg        = 20'h0_0040,
    TcdmAccessedReg     = 20'h0_FFF0,
    TcdmCongestedReg    = 20'h0_FFF8,
    PerfCounterBase     = 20'h1_0000
  } cluster_peripheral_addr_e;

  // Offload to shared accelerator
  function automatic logic shared_offload (logic [31:0] instr);
    logic offload;
    unique casez (instr)
      riscv_instr::MUL,
      riscv_instr::MULH,
      riscv_instr::MULHSU,
      riscv_instr::MULHU,
      riscv_instr::DIV,
      riscv_instr::DIVU,
      riscv_instr::REM,
      riscv_instr::REMU,
      riscv_instr::MULW,
      riscv_instr::DIVW,
      riscv_instr::DIVUW,
      riscv_instr::REMW,
      riscv_instr::REMUW: offload = 1;
      default: offload = 0;
    endcase
    return offload;
  endfunction

  // Offload to the DMA
  function automatic logic dma_offload (logic [31:0] instr);
    logic offload;
    unique casez (instr)
      riscv_instr::DM_SRC,
      riscv_instr::DM_DST,
      riscv_instr::DM_STRTI,
      riscv_instr::DM_STRT,
      riscv_instr::DM_STATI,
      riscv_instr::DM_STAT,
      riscv_instr::DM_ERRI,
      riscv_instr::DM_ERR,
      riscv_instr::DM_TWOD_STRD,
      riscv_instr::DM_TWOD_REPS: offload = 1;
      default: offload = 0;
    endcase
    return offload;
  endfunction

  // Event strobes per core, counted by the performance counters in the cluster
  // peripherals.
  typedef struct packed {
    logic issue_fpu;          // core operations performed in the FPU
    logic issue_fpu_seq;      // includes load/store operations
    logic issue_core_to_fpu;  // instructions issued from core to FPU
  } core_events_t;

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

  // Trace-Port Definitions
  typedef struct packed {
    longint acc_q_hs;
    longint fpu_out_hs;
    longint lsu_q_hs;
    longint op_in;
    longint rs1;
    longint rs2;
    longint rs3;
    longint rd;
    longint op_sel_0;
    longint op_sel_1;
    longint op_sel_2;
    longint src_fmt;
    longint dst_fmt;
    longint int_fmt;
    longint acc_qdata_0;
    longint acc_qdata_1;
    longint acc_qdata_2;
    longint op_0;
    longint op_1;
    longint op_2;
    longint use_fpu;
    longint fpu_in_rd;
    longint fpu_in_acc;
    longint ls_size;
    longint is_load;
    longint is_store;
    longint lsu_qaddr;
    longint lsu_rd;
    longint acc_wb_ready;
    longint fpu_out_acc;
    longint fpr_waddr;
    longint fpr_wdata;
    longint fpr_we;
  } fpu_trace_port_t;

  typedef struct packed {
    longint cbuf_push;
    longint is_outer;
    longint max_inst;
    longint max_rpt;
    longint stg_max;
    longint stg_mask;
  } fpu_sequencer_trace_port_t;

endpackage
