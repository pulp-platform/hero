// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Control and Status Registers                               //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Control and Status Registers (CSRs) loosely following the  //
//                 RiscV draft priviledged instruction set spec (v1.9)        //
//                 Added Floating point support                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`define ASIC_SYNTHESIS

module riscv_cs_registers import riscv_defines::*;
#(
  parameter N_HWLP        = 2,
  parameter N_HWLP_BITS   = $clog2(N_HWLP),
  parameter N_EXT_CNT     = 0,
  parameter APU           = 0,
  parameter FPU           = 0,
  parameter PULP_SECURE   = 0,
  parameter USE_PMP       = 0,
  parameter NUM_MHPMCOUNTERS = 2,
  parameter SIM_COUNT_HPMEVENTS = 1'b0,
  parameter N_PMP_ENTRIES = 16
)
(
  // Clock and Reset
  input  logic            clk,
  input  logic            rst_n,

  // Core and Cluster ID
  input  logic  [3:0]     core_id_i,
  input  logic  [5:0]     cluster_id_i,
  output logic [23:0]     mtvec_o,
  output logic [23:0]     utvec_o,

  // Used for boot address
  input  logic [30:0]     boot_addr_i,

  // Interface to registers (SRAM like)
  input  logic            csr_access_i,
  input  logic [11:0]     csr_addr_i,
  input  logic [31:0]     csr_wdata_i,
  input  logic  [1:0]     csr_op_i,
  output logic [31:0]     csr_rdata_o,

  output logic [2:0]         frm_o,
  output logic [C_PC-1:0]    fprec_o,
  input  logic [C_FFLAG-1:0] fflags_i,
  input  logic               fflags_we_i,

  // Interrupts
  output logic            m_irq_enable_o,
  output logic            u_irq_enable_o,

  //csr_irq_sec_i is always 0 if PULP_SECURE is zero
  input  logic            csr_irq_sec_i,
  output logic            sec_lvl_o,
  output logic [31:0]     mepc_o,
  output logic [31:0]     uepc_o,

  // debug
  input  logic            debug_mode_i,
  input  logic  [2:0]     debug_cause_i,
  input  logic            debug_csr_save_i,
  output logic [31:0]     depc_o,
  output logic            debug_single_step_o,
  output logic            debug_ebreakm_o,
  output logic            debug_ebreaku_o,


  output logic  [N_PMP_ENTRIES-1:0] [31:0] pmp_addr_o,
  output logic  [N_PMP_ENTRIES-1:0] [7:0]  pmp_cfg_o,

  output PrivLvl_t        priv_lvl_o,

  input  logic [31:0]     pc_if_i,
  input  logic [31:0]     pc_id_i,
  input  logic [31:0]     pc_ex_i,

  input  logic            csr_save_if_i,
  input  logic            csr_save_id_i,
  input  logic            csr_save_ex_i,

  input  logic            csr_restore_mret_i,
  input  logic            csr_restore_uret_i,

  input  logic            csr_restore_dret_i,
  //coming from controller
  input  logic [5:0]      csr_cause_i,
  //coming from controller
  input  logic            csr_save_cause_i,
  // Hardware loops
  input  logic [N_HWLP-1:0] [31:0] hwlp_start_i,
  input  logic [N_HWLP-1:0] [31:0] hwlp_end_i,
  input  logic [N_HWLP-1:0] [31:0] hwlp_cnt_i,

  output logic [31:0]              hwlp_data_o,
  output logic [N_HWLP_BITS-1:0]   hwlp_regid_o,
  output logic [2:0]               hwlp_we_o,

  // Stack Protection
  output logic [31:0]     stack_base_o,
  output logic [31:0]     stack_limit_o,

  // Performance Counters
  input  logic                 id_valid_i,        // ID stage is done
  input  logic                 is_compressed_i,   // compressed instruction in ID
  input  logic                 is_decoding_i,     // controller is in DECODE state

  input  logic                 imiss_i,           // instruction fetch
  input  logic                 pc_set_i,          // pc was set to a new value
  input  logic                 jump_i,            // jump instruction seen   (j, jr, jal, jalr)
  input  logic                 branch_i,          // branch instruction seen (bf, bnf)
  input  logic                 branch_taken_i,    // branch was taken
  input  logic                 ld_stall_i,        // load use hazard
  input  logic                 jr_stall_i,        // jump register use hazard
  input  logic                 pipeline_stall_i,  // extra cycles from elw

  input  logic                 apu_typeconflict_i,
  input  logic                 apu_contention_i,
  input  logic                 apu_dep_i,
  input  logic                 apu_wb_i,

  input  logic                 mem_load_i,        // load from memory in this cycle
  input  logic                 mem_store_i,       // store to memory in this cycle

  input  logic [N_EXT_CNT-1:0] ext_counters_i
);

  localparam N_APU_CNT       = (APU==1) ? 4 : 0;
  localparam N_PERF_COUNTERS = 12 + N_EXT_CNT + N_APU_CNT;

  localparam PERF_EXT_ID     = 12;
  localparam PERF_APU_ID     = PERF_EXT_ID + N_EXT_CNT;
  localparam MTVEC_MODE      = 2'b01;

  localparam MAX_N_PMP_ENTRIES = 16;
  localparam MAX_N_PMP_CFG     =  4;
  localparam N_PMP_CFG         = N_PMP_ENTRIES % 4 == 0 ? N_PMP_ENTRIES/4 : N_PMP_ENTRIES/4 + 1;


`ifdef ASIC_SYNTHESIS
  localparam N_PERF_REGS     = 4;
  localparam PERF_REG_ADDR_WIDTH = cf_math_pkg::idx_width(N_PERF_REGS);
`else
  localparam N_PERF_REGS     = N_PERF_COUNTERS;
`endif

  `define MSTATUS_UIE_BITS        0
  `define MSTATUS_SIE_BITS        1
  `define MSTATUS_MIE_BITS        3
  `define MSTATUS_UPIE_BITS       4
  `define MSTATUS_SPIE_BITS       5
  `define MSTATUS_MPIE_BITS       7
  `define MSTATUS_SPP_BITS        8
  `define MSTATUS_MPP_BITS    12:11
  `define MSTATUS_MPRV_BITS      17

  // misa
  localparam logic [1:0] MXL = 2'd1; // M-XLEN: XLEN in M-Mode for RV32
  localparam logic [31:0] MISA_VALUE =
      (0                <<  0)  // A - Atomic Instructions extension
    | (1                <<  2)  // C - Compressed extension
    | (0                <<  3)  // D - Double precision floating-point extension
    | (0                <<  4)  // E - RV32E base ISA
    | (32'(FPU)         <<  5)  // F - Single precision floating-point extension
    | (1                <<  8)  // I - RV32I/64I/128I base ISA
    | (1                << 12)  // M - Integer Multiply/Divide extension
    | (0                << 13)  // N - User level interrupts supported
    | (0                << 18)  // S - Supervisor mode implemented
    | (32'(PULP_SECURE) << 20)  // U - User mode implemented
    | (1                << 23)  // X - Non-standard extensions present
    | (32'(MXL)         << 30); // M-XLEN

  typedef struct packed {
    logic uie;
    // logic sie;      - unimplemented, hardwired to '0
    // logic hie;      - unimplemented, hardwired to '0
    logic mie;
    logic upie;
    // logic spie;     - unimplemented, hardwired to '0
    // logic hpie;     - unimplemented, hardwired to '0
    logic mpie;
    // logic spp;      - unimplemented, hardwired to '0
    // logic[1:0] hpp; - unimplemented, hardwired to '0
    PrivLvl_t mpp;
    logic mprv;
  } Status_t;


  typedef struct packed{
      logic [31:28] xdebugver;
      logic [27:16] zero2;
      logic         ebreakm;
      logic         zero1;
      logic         ebreaks;
      logic         ebreaku;
      logic         stepie;
      logic         stopcount;
      logic         stoptime;
      logic [8:6]   cause;
      logic         zero0;
      logic         mprven;
      logic         nmip;
      logic         step;
      PrivLvl_t     prv;
  } Dcsr_t;

  typedef struct packed {
   logic  [MAX_N_PMP_ENTRIES-1:0] [31:0] pmpaddr;
   logic  [MAX_N_PMP_CFG-1:0]     [31:0] pmpcfg_packed;
   logic  [MAX_N_PMP_ENTRIES-1:0] [ 7:0] pmpcfg;
  } Pmp_t;


  // CSR update logic
  logic [31:0] csr_wdata_int;
  logic [31:0] csr_rdata_int;
  logic        csr_we_int;
  logic [C_RM-1:0]     frm_q, frm_n;
  logic [C_FFLAG-1:0]  fflags_q, fflags_n;
  logic [C_PC-1:0]     fprec_q, fprec_n;

  // Interrupt control signals
  logic [31:0] mepc_q, mepc_n;
  logic [31:0] uepc_q, uepc_n;
  Dcsr_t       dcsr_q, dcsr_n;
  logic [31:0] depc_q, depc_n;
  logic [31:0] dscratch0_q, dscratch0_n;
  logic [31:0] dscratch1_q, dscratch1_n;
  logic [31:0] mscratch_q, mscratch_n;

  logic [31:0] exception_pc;
  Status_t mstatus_q, mstatus_n;
  logic [ 5:0] mcause_q, mcause_n;
  logic [ 5:0] ucause_q, ucause_n;
  logic [31:0] stack_base_q, stack_base_n,
               stack_size_q, stack_size_n;
  //not implemented yet
  logic [23:0] mtvec_n, mtvec_q;
  logic [23:0] utvec_n, utvec_q;

  logic is_irq;
  PrivLvl_t priv_lvl_n, priv_lvl_q, priv_lvl_reg_q;
  Pmp_t pmp_reg_q, pmp_reg_n;
  //clock gating for pmp regs
  logic [MAX_N_PMP_ENTRIES-1:0] pmpaddr_we;
  logic [MAX_N_PMP_ENTRIES-1:0] pmpcfg_we;

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Hardware Performance Monitor (HPM) Constants and Signals
  //////////////////////////////////////////////////////////////////////////////////////////////////
  localparam int unsigned NUM_INTERNAL_EVENTS = 15;
  localparam int unsigned NUM_HPMEVENTS = NUM_INTERNAL_EVENTS + N_EXT_CNT;
  localparam int unsigned HPM_EVENT_IDX_WIDTH = cf_math_pkg::idx_width(NUM_HPMEVENTS);

  logic [31:0]  mcounteren_d, mcounteren_q;

  logic [31:0]  mcountinhibit_d, mcountinhibit_q;

  logic [31:0][31:0]  mhpmcounter_q;
  logic [31:0]        mhpmcounter_increment,
                      mhpmcounter_write_lower;

  logic [31:0][HPM_EVENT_IDX_WIDTH-1:0] mhpmevent_d, mhpmevent_q;


  assign is_irq = csr_cause_i[5];

  ////////////////////////////////////////////
  //   ____ ____  ____    ____              //
  //  / ___/ ___||  _ \  |  _ \ ___  __ _   //
  // | |   \___ \| |_) | | |_) / _ \/ _` |  //
  // | |___ ___) |  _ <  |  _ <  __/ (_| |  //
  //  \____|____/|_| \_\ |_| \_\___|\__, |  //
  //                                |___/   //
  ////////////////////////////////////////////


   genvar j;


if(PULP_SECURE==1) begin
  // read logic
  always_comb
  begin
    case (csr_addr_i)
      // fcsr: Floating-Point Control and Status Register (frm + fflags).
      12'h001: csr_rdata_int = (FPU == 1) ? {27'b0, fflags_q}        : '0;
      12'h002: csr_rdata_int = (FPU == 1) ? {29'b0, frm_q}           : '0;
      12'h003: csr_rdata_int = (FPU == 1) ? {24'b0, frm_q, fflags_q} : '0;
      12'h006: csr_rdata_int = (FPU == 1) ? {27'b0, fprec_q}         : '0; // Optional precision control for FP DIV/SQRT Unit
      // mstatus
      12'h300: csr_rdata_int = {
                                  14'b0,
                                  mstatus_q.mprv,
                                  4'b0,
                                  mstatus_q.mpp,
                                  3'b0,
                                  mstatus_q.mpie,
                                  2'h0,
                                  mstatus_q.upie,
                                  mstatus_q.mie,
                                  2'h0,
                                  mstatus_q.uie
                                };

      // misa: machine isa register
      12'h301: csr_rdata_int = MISA_VALUE;
      // mtvec: machine trap-handler base address
      12'h305: csr_rdata_int = {mtvec_q, 6'h0, MTVEC_MODE};

      CSR_MCOUNTEREN: csr_rdata_int = mcounteren_q;
      CSR_MCOUNTINHIBIT: csr_rdata_int = mcountinhibit_q;

      CSR_MHPMEVENT3:   csr_rdata_int = mhpmevent_q[ 3];
      CSR_MHPMEVENT4:   csr_rdata_int = mhpmevent_q[ 4];
      CSR_MHPMEVENT5:   csr_rdata_int = mhpmevent_q[ 5];
      CSR_MHPMEVENT6:   csr_rdata_int = mhpmevent_q[ 6];
      CSR_MHPMEVENT7:   csr_rdata_int = mhpmevent_q[ 7];
      CSR_MHPMEVENT8:   csr_rdata_int = mhpmevent_q[ 8];
      CSR_MHPMEVENT9:   csr_rdata_int = mhpmevent_q[ 9];
      CSR_MHPMEVENT10:  csr_rdata_int = mhpmevent_q[10];
      CSR_MHPMEVENT11:  csr_rdata_int = mhpmevent_q[11];
      CSR_MHPMEVENT12:  csr_rdata_int = mhpmevent_q[12];
      CSR_MHPMEVENT13:  csr_rdata_int = mhpmevent_q[13];
      CSR_MHPMEVENT14:  csr_rdata_int = mhpmevent_q[14];
      CSR_MHPMEVENT15:  csr_rdata_int = mhpmevent_q[15];
      CSR_MHPMEVENT16:  csr_rdata_int = mhpmevent_q[16];
      CSR_MHPMEVENT17:  csr_rdata_int = mhpmevent_q[17];
      CSR_MHPMEVENT18:  csr_rdata_int = mhpmevent_q[18];
      CSR_MHPMEVENT19:  csr_rdata_int = mhpmevent_q[19];
      CSR_MHPMEVENT20:  csr_rdata_int = mhpmevent_q[20];
      CSR_MHPMEVENT21:  csr_rdata_int = mhpmevent_q[21];
      CSR_MHPMEVENT22:  csr_rdata_int = mhpmevent_q[22];
      CSR_MHPMEVENT23:  csr_rdata_int = mhpmevent_q[23];
      CSR_MHPMEVENT24:  csr_rdata_int = mhpmevent_q[24];
      CSR_MHPMEVENT25:  csr_rdata_int = mhpmevent_q[25];
      CSR_MHPMEVENT26:  csr_rdata_int = mhpmevent_q[26];
      CSR_MHPMEVENT27:  csr_rdata_int = mhpmevent_q[27];
      CSR_MHPMEVENT28:  csr_rdata_int = mhpmevent_q[28];
      CSR_MHPMEVENT29:  csr_rdata_int = mhpmevent_q[29];
      CSR_MHPMEVENT30:  csr_rdata_int = mhpmevent_q[30];
      CSR_MHPMEVENT31:  csr_rdata_int = mhpmevent_q[31];

      // mscratch: machine scratch
      12'h340: csr_rdata_int = mscratch_q;
      // mepc: exception program counter
      12'h341: csr_rdata_int = mepc_q;
      // mcause: exception cause
      12'h342: csr_rdata_int = {mcause_q[5], 26'b0, mcause_q[4:0]};
      // stack base and size
      12'h400: csr_rdata_int = stack_base_q;
      12'h404: csr_rdata_int = stack_size_q;

      CSR_MCYCLE:         csr_rdata_int = mhpmcounter_q[ 0];
      CSR_MINSTRET:       csr_rdata_int = mhpmcounter_q[ 2];
      CSR_MHPMCOUNTER3:   csr_rdata_int = mhpmcounter_q[ 3];
      CSR_MHPMCOUNTER4:   csr_rdata_int = mhpmcounter_q[ 4];
      CSR_MHPMCOUNTER5:   csr_rdata_int = mhpmcounter_q[ 5];
      CSR_MHPMCOUNTER6:   csr_rdata_int = mhpmcounter_q[ 6];
      CSR_MHPMCOUNTER7:   csr_rdata_int = mhpmcounter_q[ 7];
      CSR_MHPMCOUNTER8:   csr_rdata_int = mhpmcounter_q[ 8];
      CSR_MHPMCOUNTER9:   csr_rdata_int = mhpmcounter_q[ 9];
      CSR_MHPMCOUNTER10:  csr_rdata_int = mhpmcounter_q[10];
      CSR_MHPMCOUNTER11:  csr_rdata_int = mhpmcounter_q[11];
      CSR_MHPMCOUNTER12:  csr_rdata_int = mhpmcounter_q[12];
      CSR_MHPMCOUNTER13:  csr_rdata_int = mhpmcounter_q[13];
      CSR_MHPMCOUNTER14:  csr_rdata_int = mhpmcounter_q[14];
      CSR_MHPMCOUNTER15:  csr_rdata_int = mhpmcounter_q[15];
      CSR_MHPMCOUNTER16:  csr_rdata_int = mhpmcounter_q[16];
      CSR_MHPMCOUNTER17:  csr_rdata_int = mhpmcounter_q[17];
      CSR_MHPMCOUNTER18:  csr_rdata_int = mhpmcounter_q[18];
      CSR_MHPMCOUNTER19:  csr_rdata_int = mhpmcounter_q[19];
      CSR_MHPMCOUNTER20:  csr_rdata_int = mhpmcounter_q[20];
      CSR_MHPMCOUNTER21:  csr_rdata_int = mhpmcounter_q[21];
      CSR_MHPMCOUNTER22:  csr_rdata_int = mhpmcounter_q[22];
      CSR_MHPMCOUNTER23:  csr_rdata_int = mhpmcounter_q[23];
      CSR_MHPMCOUNTER24:  csr_rdata_int = mhpmcounter_q[24];
      CSR_MHPMCOUNTER25:  csr_rdata_int = mhpmcounter_q[25];
      CSR_MHPMCOUNTER26:  csr_rdata_int = mhpmcounter_q[26];
      CSR_MHPMCOUNTER27:  csr_rdata_int = mhpmcounter_q[27];
      CSR_MHPMCOUNTER28:  csr_rdata_int = mhpmcounter_q[28];
      CSR_MHPMCOUNTER29:  csr_rdata_int = mhpmcounter_q[29];
      CSR_MHPMCOUNTER30:  csr_rdata_int = mhpmcounter_q[30];
      CSR_MHPMCOUNTER31:  csr_rdata_int = mhpmcounter_q[31];

      // mhartid: unique hardware thread id
      12'hF14: csr_rdata_int = {21'b0, cluster_id_i[5:0], 1'b0, core_id_i[3:0]};

      CSR_DCSR:
               csr_rdata_int = dcsr_q;//
      CSR_DPC:
               csr_rdata_int = depc_q;
      CSR_DSCRATCH0:
               csr_rdata_int = dscratch0_q;//
      CSR_DSCRATCH1:
               csr_rdata_int = dscratch1_q;//

      // hardware loops  (not official)
      HWLoop0_START: csr_rdata_int = hwlp_start_i[0];
      HWLoop0_END: csr_rdata_int = hwlp_end_i[0];
      HWLoop0_COUNTER: csr_rdata_int = hwlp_cnt_i[0];
      HWLoop1_START: csr_rdata_int = hwlp_start_i[1];
      HWLoop1_END: csr_rdata_int = hwlp_end_i[1];
      HWLoop1_COUNTER: csr_rdata_int = hwlp_cnt_i[1];

      // PMP config registers
      12'h3A0: csr_rdata_int = USE_PMP ? pmp_reg_q.pmpcfg_packed[0] : '0;
      12'h3A1: csr_rdata_int = USE_PMP ? pmp_reg_q.pmpcfg_packed[1] : '0;
      12'h3A2: csr_rdata_int = USE_PMP ? pmp_reg_q.pmpcfg_packed[2] : '0;
      12'h3A3: csr_rdata_int = USE_PMP ? pmp_reg_q.pmpcfg_packed[3] : '0;

      12'h3Bx: csr_rdata_int = USE_PMP ? pmp_reg_q.pmpaddr[csr_addr_i[3:0]] : '0;

      /* USER CSR */
      // ustatus
      12'h000: csr_rdata_int = {
                                  27'b0,
                                  mstatus_q.upie,
                                  3'h0,
                                  mstatus_q.uie
                                };
      // utvec: user trap-handler base address
      12'h005: csr_rdata_int = {utvec_q, 6'h0, MTVEC_MODE};
      // dublicated mhartid: unique hardware thread id (not official)
      12'h014: csr_rdata_int = {21'b0, cluster_id_i[5:0], 1'b0, core_id_i[3:0]};
      // uepc: exception program counter
      12'h041: csr_rdata_int = uepc_q;
      // ucause: exception cause
      12'h042: csr_rdata_int = {ucause_q[5], 26'h0, ucause_q[4:0]};
      // current priv level (not official)
      12'hC10: csr_rdata_int = {30'h0, priv_lvl_q};
      default:
        csr_rdata_int = '0;
    endcase
  end
end else begin //PULP_SECURE == 0
  // read logic
  always_comb
  begin

    case (csr_addr_i)
      // fcsr: Floating-Point Control and Status Register (frm + fflags).
      12'h001: csr_rdata_int = (FPU == 1) ? {27'b0, fflags_q}        : '0;
      12'h002: csr_rdata_int = (FPU == 1) ? {29'b0, frm_q}           : '0;
      12'h003: csr_rdata_int = (FPU == 1) ? {24'b0, frm_q, fflags_q} : '0;
      12'h006: csr_rdata_int = (FPU == 1) ? {27'b0, fprec_q}         : '0; // Optional precision control for FP DIV/SQRT Unit
      // mstatus: always M-mode, contains IE bit
      12'h300: csr_rdata_int = {
                                  14'b0,
                                  mstatus_q.mprv,
                                  4'b0,
                                  mstatus_q.mpp,
                                  3'b0,
                                  mstatus_q.mpie,
                                  2'h0,
                                  mstatus_q.upie,
                                  mstatus_q.mie,
                                  2'h0,
                                  mstatus_q.uie
                                };
      // misa: machine isa register
      12'h301: csr_rdata_int = MISA_VALUE;
      // mtvec: machine trap-handler base address
      12'h305: csr_rdata_int = {mtvec_q, 6'h0, MTVEC_MODE};

      CSR_MCOUNTEREN: csr_rdata_int = mcounteren_q;
      CSR_MCOUNTINHIBIT: csr_rdata_int = mcountinhibit_q;

      CSR_MHPMEVENT3:   csr_rdata_int = mhpmevent_q[ 3];
      CSR_MHPMEVENT4:   csr_rdata_int = mhpmevent_q[ 4];
      CSR_MHPMEVENT5:   csr_rdata_int = mhpmevent_q[ 5];
      CSR_MHPMEVENT6:   csr_rdata_int = mhpmevent_q[ 6];
      CSR_MHPMEVENT7:   csr_rdata_int = mhpmevent_q[ 7];
      CSR_MHPMEVENT8:   csr_rdata_int = mhpmevent_q[ 8];
      CSR_MHPMEVENT9:   csr_rdata_int = mhpmevent_q[ 9];
      CSR_MHPMEVENT10:  csr_rdata_int = mhpmevent_q[10];
      CSR_MHPMEVENT11:  csr_rdata_int = mhpmevent_q[11];
      CSR_MHPMEVENT12:  csr_rdata_int = mhpmevent_q[12];
      CSR_MHPMEVENT13:  csr_rdata_int = mhpmevent_q[13];
      CSR_MHPMEVENT14:  csr_rdata_int = mhpmevent_q[14];
      CSR_MHPMEVENT15:  csr_rdata_int = mhpmevent_q[15];
      CSR_MHPMEVENT16:  csr_rdata_int = mhpmevent_q[16];
      CSR_MHPMEVENT17:  csr_rdata_int = mhpmevent_q[17];
      CSR_MHPMEVENT18:  csr_rdata_int = mhpmevent_q[18];
      CSR_MHPMEVENT19:  csr_rdata_int = mhpmevent_q[19];
      CSR_MHPMEVENT20:  csr_rdata_int = mhpmevent_q[20];
      CSR_MHPMEVENT21:  csr_rdata_int = mhpmevent_q[21];
      CSR_MHPMEVENT22:  csr_rdata_int = mhpmevent_q[22];
      CSR_MHPMEVENT23:  csr_rdata_int = mhpmevent_q[23];
      CSR_MHPMEVENT24:  csr_rdata_int = mhpmevent_q[24];
      CSR_MHPMEVENT25:  csr_rdata_int = mhpmevent_q[25];
      CSR_MHPMEVENT26:  csr_rdata_int = mhpmevent_q[26];
      CSR_MHPMEVENT27:  csr_rdata_int = mhpmevent_q[27];
      CSR_MHPMEVENT28:  csr_rdata_int = mhpmevent_q[28];
      CSR_MHPMEVENT29:  csr_rdata_int = mhpmevent_q[29];
      CSR_MHPMEVENT30:  csr_rdata_int = mhpmevent_q[30];
      CSR_MHPMEVENT31:  csr_rdata_int = mhpmevent_q[31];

      // mscratch: machine scratch
      12'h340: csr_rdata_int = mscratch_q;
      // mepc: exception program counter
      12'h341: csr_rdata_int = mepc_q;
      // mcause: exception cause
      12'h342: csr_rdata_int = {mcause_q[5], 26'b0, mcause_q[4:0]};
      // stack base and size
      12'h400: csr_rdata_int = stack_base_q;
      12'h404: csr_rdata_int = stack_size_q;

      CSR_MCYCLE:         csr_rdata_int = mhpmcounter_q[ 0];
      CSR_MINSTRET:       csr_rdata_int = mhpmcounter_q[ 2];
      CSR_MHPMCOUNTER3:   csr_rdata_int = mhpmcounter_q[ 3];
      CSR_MHPMCOUNTER4:   csr_rdata_int = mhpmcounter_q[ 4];
      CSR_MHPMCOUNTER5:   csr_rdata_int = mhpmcounter_q[ 5];
      CSR_MHPMCOUNTER6:   csr_rdata_int = mhpmcounter_q[ 6];
      CSR_MHPMCOUNTER7:   csr_rdata_int = mhpmcounter_q[ 7];
      CSR_MHPMCOUNTER8:   csr_rdata_int = mhpmcounter_q[ 8];
      CSR_MHPMCOUNTER9:   csr_rdata_int = mhpmcounter_q[ 9];
      CSR_MHPMCOUNTER10:  csr_rdata_int = mhpmcounter_q[10];
      CSR_MHPMCOUNTER11:  csr_rdata_int = mhpmcounter_q[11];
      CSR_MHPMCOUNTER12:  csr_rdata_int = mhpmcounter_q[12];
      CSR_MHPMCOUNTER13:  csr_rdata_int = mhpmcounter_q[13];
      CSR_MHPMCOUNTER14:  csr_rdata_int = mhpmcounter_q[14];
      CSR_MHPMCOUNTER15:  csr_rdata_int = mhpmcounter_q[15];
      CSR_MHPMCOUNTER16:  csr_rdata_int = mhpmcounter_q[16];
      CSR_MHPMCOUNTER17:  csr_rdata_int = mhpmcounter_q[17];
      CSR_MHPMCOUNTER18:  csr_rdata_int = mhpmcounter_q[18];
      CSR_MHPMCOUNTER19:  csr_rdata_int = mhpmcounter_q[19];
      CSR_MHPMCOUNTER20:  csr_rdata_int = mhpmcounter_q[20];
      CSR_MHPMCOUNTER21:  csr_rdata_int = mhpmcounter_q[21];
      CSR_MHPMCOUNTER22:  csr_rdata_int = mhpmcounter_q[22];
      CSR_MHPMCOUNTER23:  csr_rdata_int = mhpmcounter_q[23];
      CSR_MHPMCOUNTER24:  csr_rdata_int = mhpmcounter_q[24];
      CSR_MHPMCOUNTER25:  csr_rdata_int = mhpmcounter_q[25];
      CSR_MHPMCOUNTER26:  csr_rdata_int = mhpmcounter_q[26];
      CSR_MHPMCOUNTER27:  csr_rdata_int = mhpmcounter_q[27];
      CSR_MHPMCOUNTER28:  csr_rdata_int = mhpmcounter_q[28];
      CSR_MHPMCOUNTER29:  csr_rdata_int = mhpmcounter_q[29];
      CSR_MHPMCOUNTER30:  csr_rdata_int = mhpmcounter_q[30];
      CSR_MHPMCOUNTER31:  csr_rdata_int = mhpmcounter_q[31];

      // mhartid: unique hardware thread id
      12'hF14: csr_rdata_int = {21'b0, cluster_id_i[5:0], 1'b0, core_id_i[3:0]};

      CSR_DCSR:
               csr_rdata_int = dcsr_q;//
      CSR_DPC:
               csr_rdata_int = depc_q;
      CSR_DSCRATCH0:
               csr_rdata_int = dscratch0_q;//
      CSR_DSCRATCH1:
               csr_rdata_int = dscratch1_q;//

      // hardware loops  (not official)
      HWLoop0_START: csr_rdata_int = hwlp_start_i[0];
      HWLoop0_END: csr_rdata_int = hwlp_end_i[0];
      HWLoop0_COUNTER: csr_rdata_int = hwlp_cnt_i[0];
      HWLoop1_START: csr_rdata_int = hwlp_start_i[1];
      HWLoop1_END: csr_rdata_int = hwlp_end_i[1];
      HWLoop1_COUNTER: csr_rdata_int = hwlp_cnt_i[1];
      /* USER CSR */
      // dublicated mhartid: unique hardware thread id (not official)
      12'h014: csr_rdata_int = {21'b0, cluster_id_i[5:0], 1'b0, core_id_i[3:0]};
      // current priv level (not official)
      12'hC10: csr_rdata_int = {30'h0, priv_lvl_q};
      default:
        csr_rdata_int = '0;
    endcase
  end
end //PULP_SECURE

if(PULP_SECURE==1) begin
  // write logic
  always_comb
  begin
    fflags_n                 = fflags_q;
    frm_n                    = frm_q;
    fprec_n                  = fprec_q;
    mscratch_n               = mscratch_q;
    mepc_n                   = mepc_q;
    uepc_n                   = uepc_q;
    depc_n                   = depc_q;
    dcsr_n                   = dcsr_q;
    dscratch0_n              = dscratch0_q;
    dscratch1_n              = dscratch1_q;

    mstatus_n                = mstatus_q;
    mcause_n                 = mcause_q;
    stack_base_n             = stack_base_q;
    stack_size_n             = stack_size_q;
    ucause_n                 = ucause_q;
    hwlp_we_o                = '0;
    hwlp_regid_o             = '0;
    exception_pc             = pc_id_i;
    priv_lvl_n               = priv_lvl_q;
    mtvec_n                  = mtvec_q;
    utvec_n                  = utvec_q;
    pmp_reg_n.pmpaddr        = pmp_reg_q.pmpaddr;
    pmp_reg_n.pmpcfg_packed  = pmp_reg_q.pmpcfg_packed;
    pmpaddr_we               = '0;
    pmpcfg_we                = '0;

    if (FPU == 1) if (fflags_we_i) fflags_n = fflags_i | fflags_q;

    casex (csr_addr_i)
      // fcsr: Floating-Point Control and Status Register (frm, fflags, fprec).
      12'h001: if (csr_we_int) fflags_n = (FPU == 1) ? csr_wdata_int[C_FFLAG-1:0] : '0;
      12'h002: if (csr_we_int) frm_n    = (FPU == 1) ? csr_wdata_int[C_RM-1:0]    : '0;
      12'h003: if (csr_we_int) begin
         fflags_n = (FPU == 1) ? csr_wdata_int[C_FFLAG-1:0]            : '0;
         frm_n    = (FPU == 1) ? csr_wdata_int[C_RM+C_FFLAG-1:C_FFLAG] : '0;
      end
      12'h006: if (csr_we_int) fprec_n = (FPU == 1) ? csr_wdata_int[C_PC-1:0]    : '0;

      // mstatus: IE bit
      12'h300: if (csr_we_int) begin
        mstatus_n = '{
          uie:  csr_wdata_int[`MSTATUS_UIE_BITS],
          mie:  csr_wdata_int[`MSTATUS_MIE_BITS],
          upie: csr_wdata_int[`MSTATUS_UPIE_BITS],
          mpie: csr_wdata_int[`MSTATUS_MPIE_BITS],
          mpp:  PrivLvl_t'(csr_wdata_int[`MSTATUS_MPP_BITS]),
          mprv: csr_wdata_int[`MSTATUS_MPRV_BITS]
        };
      end
      // mtvec: machine trap-handler base address
      12'h305: if (csr_we_int) begin
        mtvec_n    = csr_wdata_int[31:8];
      end
      // mscratch: machine scratch
      12'h340: if (csr_we_int) begin
        mscratch_n = csr_wdata_int;
      end
      // mepc: exception program counter
      12'h341: if (csr_we_int) begin
        mepc_n = csr_wdata_int & ~32'b1; // force 16-bit alignment
      end
      // mcause
      12'h342: if (csr_we_int) mcause_n = {csr_wdata_int[31], csr_wdata_int[4:0]};

      CSR_DCSR:
               if (csr_we_int)
               begin
                    dcsr_n = csr_wdata_int;
                    //31:28 xdebuger = 4 -> debug is implemented
                    dcsr_n.xdebugver=4'h4;
                    //privilege level: 0-> U;1-> S; 3->M.
                    dcsr_n.prv=priv_lvl_q;
                    //currently not supported:
                    dcsr_n.nmip=1'b0;   //nmip
                    dcsr_n.mprven=1'b0; //mprven
                    dcsr_n.stopcount=1'b0;   //stopcount
                    dcsr_n.stoptime=1'b0;  //stoptime
               end
      CSR_DPC:
               if (csr_we_int)
               begin
                    depc_n = csr_wdata_int & ~32'b1; // force 16-bit alignment
               end

      CSR_DSCRATCH0:
               if (csr_we_int)
               begin
                    dscratch0_n = csr_wdata_int;
               end

      CSR_DSCRATCH1:
               if (csr_we_int)
               begin
                    dscratch1_n = csr_wdata_int;
               end

      // stack base and size
      12'h400: if (csr_we_int) stack_base_n = csr_wdata_int;
      12'h404: if (csr_we_int) stack_size_n = csr_wdata_int;

      // hardware loops
      HWLoop0_START:   if (csr_we_int) begin hwlp_we_o = 3'b001; hwlp_regid_o = 1'b0; end
      HWLoop0_END:     if (csr_we_int) begin hwlp_we_o = 3'b010; hwlp_regid_o = 1'b0; end
      HWLoop0_COUNTER: if (csr_we_int) begin hwlp_we_o = 3'b100; hwlp_regid_o = 1'b0; end
      HWLoop1_START:   if (csr_we_int) begin hwlp_we_o = 3'b001; hwlp_regid_o = 1'b1; end
      HWLoop1_END:     if (csr_we_int) begin hwlp_we_o = 3'b010; hwlp_regid_o = 1'b1; end
      HWLoop1_COUNTER: if (csr_we_int) begin hwlp_we_o = 3'b100; hwlp_regid_o = 1'b1; end


      // PMP config registers
      12'h3A0: if (csr_we_int) begin pmp_reg_n.pmpcfg_packed[0] = csr_wdata_int; pmpcfg_we[3:0]   = 4'b1111; end
      12'h3A1: if (csr_we_int) begin pmp_reg_n.pmpcfg_packed[1] = csr_wdata_int; pmpcfg_we[7:4]   = 4'b1111; end
      12'h3A2: if (csr_we_int) begin pmp_reg_n.pmpcfg_packed[2] = csr_wdata_int; pmpcfg_we[11:8]  = 4'b1111; end
      12'h3A3: if (csr_we_int) begin pmp_reg_n.pmpcfg_packed[3] = csr_wdata_int; pmpcfg_we[15:12] = 4'b1111; end

      12'h3BX: if (csr_we_int) begin pmp_reg_n.pmpaddr[csr_addr_i[3:0]]   = csr_wdata_int; pmpaddr_we[csr_addr_i[3:0]] = 1'b1;  end


      /* USER CSR */
      // ucause: exception cause
      12'h000: if (csr_we_int) begin
        mstatus_n = '{
          uie:  csr_wdata_int[`MSTATUS_UIE_BITS],
          mie:  mstatus_q.mie,
          upie: csr_wdata_int[`MSTATUS_UPIE_BITS],
          mpie: mstatus_q.mpie,
          mpp:  mstatus_q.mpp,
          mprv: mstatus_q.mprv
        };
      end
      // utvec: user trap-handler base address
      12'h005: if (csr_we_int) begin
        utvec_n    = csr_wdata_int[31:8];
      end
      // uepc: exception program counter
      12'h041: if (csr_we_int) begin
        uepc_n     = csr_wdata_int;
      end
      // ucause: exception cause
      12'h042: if (csr_we_int) ucause_n = {csr_wdata_int[31], csr_wdata_int[4:0]};
    endcase

    // exception controller gets priority over other writes
    unique case (1'b1)

      csr_save_cause_i: begin

        unique case (1'b1)
          csr_save_if_i:
            exception_pc = pc_if_i;
          csr_save_id_i:
            exception_pc = pc_id_i;
          csr_save_ex_i:
            exception_pc = pc_ex_i;
          default:;
        endcase

        unique case (priv_lvl_q)

          PRIV_LVL_U: begin
            if(~is_irq) begin
              //Exceptions, Ecall U --> M
              priv_lvl_n     = PRIV_LVL_M;
              mstatus_n.mpie = mstatus_q.uie;
              mstatus_n.mie  = 1'b0;
              mstatus_n.mpp  = PRIV_LVL_U;
              // TODO: correctly handled?
              if (debug_csr_save_i)
                  depc_n = exception_pc;
              else
                  mepc_n = exception_pc;
              mcause_n       = csr_cause_i;

            end
            else begin
              if(~csr_irq_sec_i) begin
              //U --> U
                priv_lvl_n     = PRIV_LVL_U;
                mstatus_n.upie = mstatus_q.uie;
                mstatus_n.uie  = 1'b0;
                // TODO: correctly handled?
                if (debug_csr_save_i)
                    depc_n = exception_pc;
                else
                    uepc_n = exception_pc;
                ucause_n       = csr_cause_i;

              end else begin
              //U --> M
                priv_lvl_n     = PRIV_LVL_M;
                mstatus_n.mpie = mstatus_q.uie;
                mstatus_n.mie  = 1'b0;
                mstatus_n.mpp  = PRIV_LVL_U;
                // TODO: correctly handled?
                if (debug_csr_save_i)
                    depc_n = exception_pc;
                else
                    mepc_n = exception_pc;
                mcause_n       = csr_cause_i;
              end
            end
          end //PRIV_LVL_U

          PRIV_LVL_M: begin
            if (debug_csr_save_i) begin
                // all interrupts are masked, don't update cause, epc, tval dpc
                // and mpstatus
                dcsr_n.prv   = PRIV_LVL_M;
                dcsr_n.cause = debug_cause_i;
                depc_n       = exception_pc;
            end else begin
                //Exceptions or Interrupts from PRIV_LVL_M always do M --> M
                priv_lvl_n     = PRIV_LVL_M;
                mstatus_n.mpie = mstatus_q.mie;
                mstatus_n.mie  = 1'b0;
                mstatus_n.mpp  = PRIV_LVL_M;
                mepc_n         = exception_pc;
                mcause_n       = csr_cause_i;
            end
          end //PRIV_LVL_M
          default:;

        endcase

      end //csr_save_cause_i

      csr_restore_uret_i: begin //URET
        //mstatus_q.upp is implicitly 0, i.e PRIV_LVL_U
        mstatus_n.uie  = mstatus_q.upie;
        priv_lvl_n     = PRIV_LVL_U;
        mstatus_n.upie = 1'b1;
      end //csr_restore_uret_i

      csr_restore_mret_i: begin //MRET
        unique case (mstatus_q.mpp)
          PRIV_LVL_U: begin
            mstatus_n.uie  = mstatus_q.mpie;
            priv_lvl_n     = PRIV_LVL_U;
            mstatus_n.mpie = 1'b1;
            mstatus_n.mpp  = PRIV_LVL_U;
          end
          PRIV_LVL_M: begin
            mstatus_n.mie  = mstatus_q.mpie;
            priv_lvl_n     = PRIV_LVL_M;
            mstatus_n.mpie = 1'b1;
            mstatus_n.mpp  = PRIV_LVL_U;
          end
          default:;
        endcase
      end //csr_restore_mret_i


      csr_restore_dret_i: begin //DRET
          // restore to the recorded privilege level
          // TODO: prevent illegal values, see riscv-debug p.44
          priv_lvl_n = dcsr_q.prv;

      end //csr_restore_dret_i

      default:;
    endcase
  end
end else begin //PULP_SECURE == 0
  // write logic
  always_comb
  begin
    fflags_n                 = fflags_q;
    frm_n                    = frm_q;
    fprec_n                  = fprec_q;
    mscratch_n               = mscratch_q;
    mepc_n                   = mepc_q;
    depc_n                   = depc_q;
    dcsr_n                   = dcsr_q;
    dscratch0_n              = dscratch0_q;
    dscratch1_n              = dscratch1_q;

    mstatus_n                = mstatus_q;
    mcause_n                 = mcause_q;
    stack_base_n             = stack_base_q;
    stack_size_n             = stack_size_q;
    hwlp_we_o                = '0;
    hwlp_regid_o             = '0;
    exception_pc             = pc_id_i;
    priv_lvl_n               = priv_lvl_q;
    mtvec_n                  = mtvec_q;
    pmp_reg_n.pmpaddr        = pmp_reg_q.pmpaddr;
    pmp_reg_n.pmpcfg_packed  = pmp_reg_q.pmpcfg_packed;
    pmpaddr_we               = '0;
    pmpcfg_we                = '0;


    if (FPU == 1) if (fflags_we_i) fflags_n = fflags_i | fflags_q;

    case (csr_addr_i)
      // fcsr: Floating-Point Control and Status Register (frm, fflags, fprec).
      12'h001: if (csr_we_int) fflags_n = (FPU == 1) ? csr_wdata_int[C_FFLAG-1:0] : '0;
      12'h002: if (csr_we_int) frm_n    = (FPU == 1) ? csr_wdata_int[C_RM-1:0]    : '0;
      12'h003: if (csr_we_int) begin
         fflags_n = (FPU == 1) ? csr_wdata_int[C_FFLAG-1:0]            : '0;
         frm_n    = (FPU == 1) ? csr_wdata_int[C_RM+C_FFLAG-1:C_FFLAG] : '0;
      end
      12'h006: if (csr_we_int) fprec_n = (FPU == 1) ? csr_wdata_int[C_PC-1:0]    : '0;

      // mstatus: IE bit
      12'h300: if (csr_we_int) begin
        mstatus_n = '{
          uie:  csr_wdata_int[`MSTATUS_UIE_BITS],
          mie:  csr_wdata_int[`MSTATUS_MIE_BITS],
          upie: csr_wdata_int[`MSTATUS_UPIE_BITS],
          mpie: csr_wdata_int[`MSTATUS_MPIE_BITS],
          mpp:  PrivLvl_t'(csr_wdata_int[`MSTATUS_MPP_BITS]),
          mprv: csr_wdata_int[`MSTATUS_MPRV_BITS]
        };
      end
      // mscratch: machine scratch
      12'h340: if (csr_we_int) begin
        mscratch_n = csr_wdata_int;
      end
      // mepc: exception program counter
      12'h341: if (csr_we_int) begin
        mepc_n = csr_wdata_int & ~32'b1; // force 16-bit alignment
      end
      // mcause
      12'h342: if (csr_we_int) mcause_n = {csr_wdata_int[31], csr_wdata_int[4:0]};

      CSR_DCSR:
               if (csr_we_int)
               begin
                    dcsr_n = csr_wdata_int;
                    //31:28 xdebuger = 4 -> debug is implemented
                    dcsr_n.xdebugver=4'h4;
                    //privilege level: 0-> U;1-> S; 3->M.
                    dcsr_n.prv=priv_lvl_q;
                    //currently not supported:
                    dcsr_n.nmip=1'b0;   //nmip
                    dcsr_n.mprven=1'b0; //mprven
                    dcsr_n.stopcount=1'b0;   //stopcount
                    dcsr_n.stoptime=1'b0;  //stoptime
               end
      CSR_DPC:
               if (csr_we_int)
               begin
                    depc_n = csr_wdata_int & ~32'b1; // force 16-bit alignment
               end

      CSR_DSCRATCH0:
               if (csr_we_int)
               begin
                    dscratch0_n = csr_wdata_int;
               end

      CSR_DSCRATCH1:
               if (csr_we_int)
               begin
                    dscratch1_n = csr_wdata_int;
               end

      // stack base and size
      12'h400: if (csr_we_int) stack_base_n = csr_wdata_int;
      12'h404: if (csr_we_int) stack_size_n = csr_wdata_int;

      // hardware loops
      HWLoop0_START: if (csr_we_int) begin hwlp_we_o = 3'b001; hwlp_regid_o = 1'b0; end
      HWLoop0_END: if (csr_we_int) begin hwlp_we_o = 3'b010; hwlp_regid_o = 1'b0; end
      HWLoop0_COUNTER: if (csr_we_int) begin hwlp_we_o = 3'b100; hwlp_regid_o = 1'b0; end
      HWLoop1_START: if (csr_we_int) begin hwlp_we_o = 3'b001; hwlp_regid_o = 1'b1; end
      HWLoop1_END: if (csr_we_int) begin hwlp_we_o = 3'b010; hwlp_regid_o = 1'b1; end
      HWLoop1_COUNTER: if (csr_we_int) begin hwlp_we_o = 3'b100; hwlp_regid_o = 1'b1; end
    endcase

    // exception controller gets priority over other writes
    unique case (1'b1)

      csr_save_cause_i: begin
        unique case (1'b1)
          csr_save_if_i:
            exception_pc = pc_if_i;
          csr_save_id_i:
            exception_pc = pc_id_i;
          default:;
        endcase

        if (debug_csr_save_i) begin
            // all interrupts are masked, don't update cause, epc, tval dpc and
            // mpstatus
            dcsr_n.prv   = PRIV_LVL_M;
            dcsr_n.cause = debug_cause_i;
            depc_n       = exception_pc;
        end else begin
            priv_lvl_n     = PRIV_LVL_M;
            mstatus_n.mpie = mstatus_q.mie;
            mstatus_n.mie  = 1'b0;
            mstatus_n.mpp  = PRIV_LVL_M;
            mepc_n = exception_pc;
            mcause_n       = csr_cause_i;
        end
      end //csr_save_cause_i

      csr_restore_mret_i: begin //MRET
        mstatus_n.mie  = mstatus_q.mpie;
        priv_lvl_n     = PRIV_LVL_M;
        mstatus_n.mpie = 1'b1;
        mstatus_n.mpp  = PRIV_LVL_M;
      end //csr_restore_mret_i

      csr_restore_dret_i: begin //DRET
        // restore to the recorded privilege level
        // TODO: prevent illegal values, see riscv-debug p.44
        priv_lvl_n = dcsr_q.prv;
      end //csr_restore_dret_i

      default:;
    endcase
  end
end //PULP_SECURE

  assign hwlp_data_o = csr_wdata_int;

  // CSR operation logic
  always_comb
  begin
    csr_wdata_int = csr_wdata_i;
    csr_we_int    = 1'b1;

    unique case (csr_op_i)
      CSR_OP_WRITE: csr_wdata_int = csr_wdata_i;
      CSR_OP_SET:   csr_wdata_int = csr_wdata_i | csr_rdata_o;
      CSR_OP_CLEAR: csr_wdata_int = (~csr_wdata_i) & csr_rdata_o;

      CSR_OP_NONE: begin
        csr_wdata_int = csr_wdata_i;
        csr_we_int    = 1'b0;
      end

      default:;
    endcase
  end


  // output mux
  always_comb
  begin
    csr_rdata_o = csr_rdata_int;
  end


  // directly output some registers
  assign m_irq_enable_o  = mstatus_q.mie & priv_lvl_q == PRIV_LVL_M;
  assign u_irq_enable_o  = mstatus_q.uie & priv_lvl_q == PRIV_LVL_U;
  assign priv_lvl_o      = priv_lvl_q;
  assign sec_lvl_o       = priv_lvl_q[0];
  assign frm_o           = (FPU == 1) ? frm_q : '0;
  assign fprec_o         = (FPU == 1) ? fprec_q : '0;

  assign mtvec_o         = mtvec_q;
  assign utvec_o         = utvec_q;

  assign mepc_o          = mepc_q;
  assign uepc_o          = uepc_q;

  assign depc_o          = depc_q;

  assign pmp_addr_o     = pmp_reg_q.pmpaddr;
  assign pmp_cfg_o      = pmp_reg_q.pmpcfg;

  assign debug_single_step_o  = dcsr_q.step;
  assign debug_ebreakm_o      = dcsr_q.ebreakm;
  assign debug_ebreaku_o      = dcsr_q.ebreaku;



  generate
  if (PULP_SECURE == 1)
  begin

    for(j=0;j<N_PMP_ENTRIES;j++)
    begin : CS_PMP_CFG
      assign pmp_reg_n.pmpcfg[j]                                 = pmp_reg_n.pmpcfg_packed[j/4][8*((j%4)+1)-1:8*(j%4)];
      assign pmp_reg_q.pmpcfg_packed[j/4][8*((j%4)+1)-1:8*(j%4)] = pmp_reg_q.pmpcfg[j];
    end

    for(j=0;j<N_PMP_ENTRIES;j++)
    begin : CS_PMP_REGS_FF
      always_ff @(posedge clk, negedge rst_n)
      begin
          if (rst_n == 1'b0)
          begin
            pmp_reg_q.pmpcfg[j]   <= '0;
            pmp_reg_q.pmpaddr[j]  <= '0;
          end
          else
          begin
            if(pmpcfg_we[j])
              pmp_reg_q.pmpcfg[j]    <= USE_PMP ? pmp_reg_n.pmpcfg[j]  : '0;
            if(pmpaddr_we[j])
              pmp_reg_q.pmpaddr[j]   <= USE_PMP ? pmp_reg_n.pmpaddr[j] : '0;
          end
        end
      end //CS_PMP_REGS_FF

      always_ff @(posedge clk, negedge rst_n)
      begin
          if (rst_n == 1'b0)
          begin
            uepc_q         <= '0;
            ucause_q       <= '0;
            mtvec_q        <= '0;
            utvec_q        <= '0;
            priv_lvl_q     <= PRIV_LVL_M;

          end
          else
          begin
            uepc_q         <= uepc_n;
            ucause_q       <= ucause_n;
            mtvec_q        <= mtvec_n;
            utvec_q        <= utvec_n;
            priv_lvl_q     <= priv_lvl_n;
          end
        end

  end
  else begin

        assign uepc_q       = '0;
        assign ucause_q     = '0;
        assign mtvec_q      = boot_addr_i[30:7];
        assign utvec_q      = '0;
        assign priv_lvl_q   = PRIV_LVL_M;

  end
  endgenerate


  // actual registers
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
    begin
      if (FPU == 1) begin
        frm_q          <= '0;
        fflags_q       <= '0;
        fprec_q        <= '0;
      end
      mstatus_q  <= '{
              uie:  1'b0,
              mie:  1'b0,
              upie: 1'b0,
              mpie: 1'b0,
              mpp:  PRIV_LVL_M,
              mprv: 1'b0
            };
      mepc_q      <= '0;
      mcause_q    <= '0;
      stack_base_q <= '0;
      stack_size_q <= '0;

      depc_q      <= '0;
      dcsr_q      <= '0;
      dcsr_q.prv  <= PRIV_LVL_M;
      dscratch0_q <= '0;
      dscratch1_q <= '0;
      mscratch_q  <= '0;
    end
    else
    begin
      // update CSRs
      if(FPU == 1) begin
        frm_q      <= frm_n;
        fflags_q   <= fflags_n;
        fprec_q    <= fprec_n;
      end
      if (PULP_SECURE == 1) begin
        mstatus_q      <= mstatus_n ;
      end else begin
        mstatus_q  <= '{
                uie:  1'b0,
                mie:  mstatus_n.mie,
                upie: 1'b0,
                mpie: mstatus_n.mpie,
                mpp:  PRIV_LVL_M,
                mprv: 1'b0
              };
      end
      mepc_q     <= mepc_n    ;
      mcause_q   <= mcause_n  ;

      depc_q     <= depc_n    ;
      dcsr_q     <= dcsr_n;
      dscratch0_q<= dscratch0_n;
      dscratch1_q<= dscratch1_n;
      mscratch_q <= mscratch_n;
      stack_base_q <= stack_base_n;
      stack_size_q <= stack_size_n;
    end
  end

  assign stack_base_o = stack_base_q;
  assign stack_limit_o = stack_base_q - stack_size_q;

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Hardware Performance Monitor (HPM) Implementation
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // HPM Events
  logic [NUM_HPMEVENTS-1:0] hpm_events;
  logic id_valid_q;
  always_comb begin
    hpm_events = '0;
    hpm_events[1]  = ld_stall_i & id_valid_q;                       // nr of load use hazards
    hpm_events[2]  = jr_stall_i & id_valid_q;                       // nr of jump register hazards
    hpm_events[3]  = imiss_i & (~pc_set_i);                         // cycles waiting for instruction fetches, excluding jumps and branches
    hpm_events[4]  = mem_load_i;                                    // nr of loads
    hpm_events[5]  = mem_store_i;                                   // nr of stores
    hpm_events[6]  = jump_i                     & id_valid_q;       // nr of jumps (unconditional)
    hpm_events[7]  = branch_i                   & id_valid_q;       // nr of branches (conditional)
    hpm_events[8]  = branch_i & branch_taken_i  & id_valid_q;       // nr of taken branches (conditional)
    hpm_events[9] = id_valid_i & is_decoding_i & is_compressed_i;   // compressed instruction counter
    hpm_events[10] = pipeline_stall_i;                              // extra cycles from ELW
    hpm_events[11] = !APU ? 1'b0 : apu_typeconflict_i & ~apu_dep_i;
    hpm_events[12] = !APU ? 1'b0 : apu_contention_i;
    hpm_events[13] = !APU ? 1'b0 : apu_dep_i & ~apu_contention_i;
    hpm_events[14] = !APU ? 1'b0 : apu_wb_i;
    hpm_events[NUM_HPMEVENTS-1:NUM_INTERNAL_EVENTS] = ext_counters_i;
  end
  always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      id_valid_q <= 1'b0;
    end else begin
      id_valid_q <= id_valid_i;
    end
  end

  // Count HPM events in simulation, so no software modifications are required to display all the
  // accumulated value of all HPM event counters at the end of simulation.
`ifndef TARGET_SYNTHESIS
// pragma translate_off
  if (SIM_COUNT_HPMEVENTS) begin : gen_sim_count_hpmevents
    typedef logic [31:0] sim_cnt_t;
    sim_cnt_t [NUM_HPMEVENTS-1:1] sim_cnt_d, sim_cnt_q;
    always_ff @(posedge clk, negedge rst_n) begin
      if (!rst_n) begin
        sim_cnt_q <= '0;
      end else begin
        sim_cnt_q <= sim_cnt_d;
      end
    end
    for (genvar i = 1; i < NUM_HPMEVENTS; i++) begin : gen_sim_cnt_d
      always_comb begin
        sim_cnt_d[i] = sim_cnt_q[i];
        if (hpm_events[i]) begin
          sim_cnt_d[i]++;
        end
      end
    end
    final begin
      for (int unsigned i = 1; i < NUM_HPMEVENTS; i++) begin
        $display("%m: counter for hpm_event[%02d] = %0d", i, sim_cnt_q[i]);
      end
    end
  end
// pragma translate_on
`endif

  // M-Mode HPM Inhibit Register
  for (genvar i = 0; i < 32; i++) begin : gen_mcountinhibit
    if (i == 1 || // counter at index 1 not implemented
        i >= (NUM_MHPMCOUNTERS + 3) // programmable counters start at index 3
    ) begin : gen_not_implemented
      assign mcountinhibit_q[i] = 1'b0;
    end else begin : gen_implemented
      always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
          mcountinhibit_q[i] <= 1'b1; // disabled after reset
        end else begin
          mcountinhibit_q[i] <= mcountinhibit_d[i];
        end
      end
    end
  end

  // M-Mode HPM Inhibit CSR Write Logic
  always_comb begin
    if (csr_we_int && csr_addr_i == CSR_MCOUNTINHIBIT) begin
      mcountinhibit_d = csr_wdata_int;
    end else begin
      mcountinhibit_d = mcountinhibit_q;
    end
  end

  // M-Mode HPM Event Registers
  for (genvar i = 0; i < 32; i++) begin : gen_mhpmevent
    // programmable HPM events start at index 3
    if (i < 3 || i >= (NUM_MHPMCOUNTERS + 3)) begin : gen_not_implemented
      assign mhpmevent_q[i] = '0;
    end else begin : gen_implemented
      always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
          mhpmevent_q[i] <= '0;
        end else begin
          mhpmevent_q[i] <= mhpmevent_d[i];
        end
      end
    end
  end

  // M-Mode HPM Event CSR Write Logic
  for (genvar i = 0; i < 32; i++) begin : gen_mhpmevent_d
    if (i == 1 || i >= (NUM_MHPMCOUNTERS + 3)) begin : gen_not_implemented
      assign mhpmevent_d[i] = '0;
    end else begin : gen_implemented
      always_comb begin
        if (csr_we_int && csr_addr_i == (CSR_MHPMEVENT3 + i - 3)) begin
          mhpmevent_d[i] = csr_wdata_int;
        end else begin
          mhpmevent_d[i] = mhpmevent_q[i];
        end
      end
    end
  end

  // M-Mode HPM Counter Registers
  for (genvar i = 0; i < 32; i++) begin : gen_mhpmcounter
    if (i == 1 || // counter at index 1 not implemented
        i >= (NUM_MHPMCOUNTERS + 3) // programmable counters start at index 3
    ) begin : gen_not_implemented
      assign mhpmcounter_q[i] = '0;
    end else begin : gen_implemented
      always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
          mhpmcounter_q[i] <= '0;
        end else begin
          if (mhpmcounter_write_lower[i]) begin
            mhpmcounter_q[i][31:0] <= csr_wdata_int;
          end else if (mhpmcounter_increment[i]) begin
            mhpmcounter_q[i] <= mhpmcounter_q[i] + 1;
          end
        end
      end
    end
  end

  // M-Mode HPM Counter CSR Write Logic
  for (genvar i = 0; i < 32; i++) begin : gen_mhpmcounter_write
    if (i == 1 || // counter at index 1 not implemented
        i >= (NUM_MHPMCOUNTERS + 3) // programmable counters start at index 3
    ) begin : gen_not_implemented
      assign mhpmcounter_write_lower[i] = 1'b0;
    end else begin : gen_implemented
      assign mhpmcounter_write_lower[i] = csr_we_int && (csr_addr_i == (CSR_MCYCLE + i));
    end
  end

  // M-Mode HPM Counter Increment Logic
  for (genvar i = 0; i < 32; i++) begin : gen_mhpmcounter_increment
    if (i == 0) begin : gen_mcycle
      assign mhpmcounter_increment[i] = ~mcountinhibit_q[i];
    end else if (i == 1) begin : gen_mtime_not_implemented
      assign mhpmcounter_increment[i] = 1'b0;
    end else if (i == 2) begin : gen_minstret
      assign mhpmcounter_increment[i] = ~mcountinhibit_q[i] & id_valid_i & is_decoding_i;
    end else if (i < (NUM_MHPMCOUNTERS + 3)) begin : gen_mhpmcounter
      assign mhpmcounter_increment[i] = ~mcountinhibit_q[i] & hpm_events[mhpmevent_q[i]];
    end else begin : gen_not_implemented
      assign mhpmcounter_increment[i] = 1'b0;
    end
  end

  // M-Mode HPM Enable Register
  for (genvar i = 0; i < 32; i++) begin : gen_mcounteren
    if (i == 1 || // counter at index 1 not implemented
        i >= (NUM_MHPMCOUNTERS + 3) // programmable counters start at index 3
    ) begin : gen_not_implemented
      assign mcounteren_q[i] = 1'b0;
    end else begin : gen_implemented
      always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
          mcounteren_q[i] <= 1'b0;
        end else begin
          mcounteren_q[i] <= mcounteren_d[i];
        end
      end
    end
  end

  // M-Mode HPM Enable CSR Write Logic
  always_comb begin
    if (csr_we_int && csr_addr_i == CSR_MCOUNTEREN) begin
      mcounteren_d = csr_wdata_int;
    end else begin
      mcounteren_d = mcounteren_q;
    end
  end

endmodule
