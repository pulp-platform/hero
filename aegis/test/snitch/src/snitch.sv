// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// Description: Top-Level of Snitch Integer Core RV32E

`include "common_cells/registers.svh"

// `SNITCH_ENABLE_PERF Enables mcycle, minstret performance counters (read only)

module snitch import snitch_pkg::*; import riscv_instr::*; #(
  parameter logic [31:0] BootAddr  = 32'h0000_1000,
  parameter logic [31:0] MTVEC     = BootAddr, // Exception Base Address (see privileged spec 3.1.7)
  parameter logic [31:0] STVEC     = BootAddr, // Exception Base Address (see privileged spec 3.1.7)
  parameter bit          RVE       = 0,   // Reduced-register extension
  parameter bit          SDMA      = 0,   // Enable Snitch DMA as accelerator
  parameter bit          RVFD      = 1,   // Enable F and D Extension
  parameter snitch_pma_pkg::snitch_pma_t SnitchPMACfg = snitch_cfg::DefaultSnitchCfg
) (
  input  logic          clk_i,
  input  logic          rst_i,
  input  logic [31:0]   hart_id_i,
  output logic          flush_i_valid_o, // instruction cache flush requst
  input  logic          flush_i_ready_i, // tie to 1'b1 if unsused
  // Instruction Refill Port
  output logic [31:0]   inst_addr_o,
  output logic          inst_cacheable_o,
  input  logic [31:0]   inst_data_i,
  output logic          inst_valid_o,
  input  logic          inst_ready_i,
`ifdef RISCV_FORMAL
  output logic [0:0]       rvfi_valid,
  output logic [0:0][63:0] rvfi_order,
  output logic [0:0][31:0] rvfi_insn,
  output logic [0:0]       rvfi_trap,
  output logic [0:0]       rvfi_halt,
  output logic [0:0]       rvfi_intr,
  output logic [0:0][1:0]  rvfi_mode,
  output logic [0:0][4:0]  rvfi_rs1_addr,
  output logic [0:0][4:0]  rvfi_rs2_addr,
  output logic [0:0][31:0] rvfi_rs1_rdata,
  output logic [0:0][31:0] rvfi_rs2_rdata,
  output logic [0:0][4:0]  rvfi_rd_addr,
  output logic [0:0][31:0] rvfi_rd_wdata,
  output logic [0:0][31:0] rvfi_pc_rdata,
  output logic [0:0][31:0] rvfi_pc_wdata,
  output logic [0:0][31:0] rvfi_mem_addr,
  output logic [0:0][3:0]  rvfi_mem_rmask,
  output logic [0:0][3:0]  rvfi_mem_wmask,
  output logic [0:0][31:0] rvfi_mem_rdata,
  output logic [0:0][31:0] rvfi_mem_wdata,
`endif
  /// Accelerator Interface - Master Port
  /// Independent channels for transaction request and read completion.
  /// AXI-like handshaking.
  /// Same IDs need to be handled in-order.
  output logic [31:0]   acc_qaddr_o,
  output logic [4:0]    acc_qid_o,
  output logic [31:0]   acc_qdata_op_o,
  output logic [63:0]   acc_qdata_arga_o,
  output logic [63:0]   acc_qdata_argb_o,
  output logic [63:0]   acc_qdata_argc_o,
  output logic          acc_qvalid_o,
  input  logic          acc_qready_i,
  input  logic [63:0]   acc_pdata_i,
  input  logic [4:0]    acc_pid_i,
  input  logic          acc_perror_i,
  input  logic          acc_pvalid_i,
  output logic          acc_pready_o,
  /// TCDM Data Interface
  /// Write transactions do not return data on the `P Channel`
  /// Transactions need to be handled strictly in-order.
  output snitch_pkg::addr_t data_qaddr_o,
  output logic              data_qwrite_o,
  output logic [3:0]        data_qamo_o,
  output logic [1:0]        data_qsize_o,
  output logic [63:0]       data_qdata_o,
  output logic [7:0]        data_qstrb_o,
  output logic              data_qvalid_o,
  input  logic              data_qready_i,
  input  logic [63:0]       data_pdata_i,
  input  logic              data_perror_i,
  input  logic              data_pvalid_i,
  output logic              data_pready_o,
  input  logic              wake_up_sync_i, // synchronous wake-up interrupt
  // FPU **un-timed** Side-channel
  output fpnew_pkg::roundmode_e fpu_rnd_mode_o,
  input  fpnew_pkg::status_t    fpu_status_i
);

  localparam int RegWidth = RVE ? 4 : 5;

  logic illegal_inst, illegal_csr;
  logic zero_lsb;

  // Instruction fetch
  logic [31:0] pc_d, pc_q;
  logic wfi_d, wfi_q;
  logic [31:0] consec_pc;
  // Immediates
  logic [31:0] iimm, uimm, jimm, bimm, simm;
  /* verilator lint_off WIDTH */
  assign iimm = $signed({inst_data_i[31:20]});
  assign uimm = {inst_data_i[31:12], 12'b0};
  assign jimm = $signed({inst_data_i[31],
                                  inst_data_i[19:12], inst_data_i[20], inst_data_i[30:21], 1'b0});
  assign bimm = $signed({inst_data_i[31],
                                    inst_data_i[7], inst_data_i[30:25], inst_data_i[11:8], 1'b0});
  assign simm = $signed({inst_data_i[31:25], inst_data_i[11:7]});
  /* verilator lint_on WIDTH */

  logic [31:0] opa, opb;
  logic [32:0] adder_result;
  logic [31:0] alu_result;

  logic [RegWidth-1:0] rd, rs1, rs2;
  logic stall, lsu_stall;
  // Register connections
  logic [1:0][RegWidth-1:0] gpr_raddr;
  logic [1:0][31:0]         gpr_rdata;
  logic [0:0][RegWidth-1:0] gpr_waddr;
  logic [0:0][31:0]         gpr_wdata;
  logic [0:0]               gpr_we;
  logic [2**RegWidth-1:0]   sb_d, sb_q;

  // Load/Store Defines
  logic is_load, is_store, is_signed;
  logic is_fp_load, is_fp_store;
  logic ls_misaligned;
  logic ld_addr_misaligned;
  logic st_addr_misaligned;

  enum logic [1:0] {
    Byte = 2'b00,
    HalfWord = 2'b01,
    Word = 2'b10,
    Double = 2'b11
  } ls_size;

  enum logic [3:0] {
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
  } ls_amo;

  logic [63:0] ld_result;
  logic lsu_qready, lsu_qvalid;
  logic lsu_pvalid, lsu_pready;
  logic [RegWidth-1:0] lsu_rd;

  logic retire_load; // retire a load instruction
  logic retire_i; // retire the rest of the base instruction set
  logic retire_acc; // retire an instruction we offloaded

  logic acc_stall;
  logic valid_instr;
  logic exception;

  // ALU Operations
  enum logic [3:0]  {
    Add, Sub,
    Slt, Sltu,
    Sll, Srl, Sra,
    LXor, LOr, LAnd, LNAnd,
    Eq, Neq, Ge, Geu,
    BypassA
  } alu_op;

  enum logic [3:0] {
    None, Reg, IImmediate, UImmediate, JImmediate, SImmediate, SFImmediate, PC, CSR, CSRImmmediate
  } opa_select, opb_select;

  logic write_rd; // write desitnation this cycle
  logic uses_rd;
  enum logic [2:0] {Consec, Alu, Exception, MRet, SRet} next_pc;

  enum logic [1:0] {RdAlu, RdConsecPC, RdBypass} rd_select;
  logic [31:0] rd_bypass;

  logic is_branch;

  // -----
  // CSRs
  // -----
  logic [31:0] csr_rvalue;
  logic csr_en;

  localparam logic M = 0;
  localparam logic S = 1;

  logic [1:0][31:0] scratch_d, scratch_q;
  logic [1:0][31:0] epc_d, epc_q;
  logic [1:0][3:0] cause_d, cause_q;
  logic spp_d, spp_q;
  snitch_pkg::priv_lvl_t mpp_d, mpp_q;
  snitch_pkg::priv_lvl_t priv_lvl_d, priv_lvl_q;

  struct packed {
    logic mode;
    logic [21:0] ppn;
  } satp_d, satp_q;

  `FFNR(scratch_q, scratch_d, clk_i)
  `FFNR(epc_q, epc_d, clk_i)
  `FFNR(satp_q, satp_d, clk_i)
  `FFSR(cause_q, cause_d, '0, clk_i, rst_i)
  `FFSR(priv_lvl_q, priv_lvl_d, snitch_pkg::PrivLvlM, clk_i, rst_i)
  `FFSR(mpp_q, mpp_d, snitch_pkg::PrivLvlU, clk_i, rst_i)
  `FFSR(spp_q, spp_d, 1'b0, clk_i, rst_i)

  typedef struct packed {
    fpnew_pkg::roundmode_e frm;
    fpnew_pkg::status_t    fflags;
  } fcsr_t;
  fcsr_t fcsr_d, fcsr_q;

  assign fpu_rnd_mode_o = fcsr_q.frm;

  // Registers
  `FFSR(pc_q, pc_d, BootAddr, clk_i, rst_i)
  `FFSR(wfi_q, wfi_d, '0, clk_i, rst_i)
  `FFSR(sb_q, sb_d, '0, clk_i, rst_i)
  `FFSR(fcsr_q, fcsr_d, '0, clk_i, rst_i)

  // performance counter
  `ifdef SNITCH_ENABLE_PERF
  logic [63:0] cycle_q;
  logic [63:0] instret_q;
  `FFSR(cycle_q, cycle_q + 1, '0, clk_i, rst_i)
  `FFLSR(instret_q, instret_q + 1, !stall, '0, clk_i, rst_i)
  `endif

  logic [snitch_pkg::PLEN-32-1:0] mseg_q, mseg_d;
  `FFSR(mseg_q, mseg_d, '0, clk_i, rst_i)

  // accelerator offloading interface
  // register int destination in scoreboard
  logic  acc_register_rd;

  assign acc_qaddr_o = hart_id_i;
  assign acc_qid_o = rd;
  assign acc_qdata_op_o = inst_data_i;
  assign acc_qdata_arga_o = {{32{gpr_rdata[0][31]}}, gpr_rdata[0]};
  assign acc_qdata_argb_o = {{32{gpr_rdata[1][31]}}, gpr_rdata[1]};
  // operand C is currently only used for load/store instructions
  assign acc_qdata_argc_o = $unsigned({mseg_q, alu_result});

  // instruction fetch interface
  assign inst_addr_o = pc_q;
  assign inst_cacheable_o = snitch_pma_pkg::is_inside_cacheable_regions(SnitchPMACfg, pc_q);
  assign inst_valid_o = ~wfi_q;

  // --------------------
  // Control
  // --------------------
  // Scoreboard: Keep track of rd dependencies (only loads at the moment)
  logic operands_ready;
  logic dst_ready;
  logic opa_ready, opb_ready;

  always_comb begin
    sb_d = sb_q;
    if (retire_load) sb_d[lsu_rd] = 1'b0;
    // only place the reservation if we actually executed the load or offload instruction
    if ((is_load | acc_register_rd) && !stall && !exception) sb_d[rd] = 1'b1;
    if (retire_acc) sb_d[acc_pid_i[RegWidth-1:0]] = 1'b0;
    sb_d[0] = 1'b0;
  end
  // TODO(zarubaf): This can probably be described a bit more efficient
  assign opa_ready = (opa_select != Reg) | ~sb_q[rs1];
  assign opb_ready = (opb_select != Reg & opb_select != SImmediate) | ~sb_q[rs2];
  assign operands_ready = opa_ready & opb_ready;
  // either we are not using the destination register or we need to make
  // sure that its destination operand is not marked busy in the scoreboard.
  assign dst_ready = ~uses_rd | (uses_rd & ~sb_q[rd]);

  assign valid_instr = (inst_ready_i & inst_valid_o) & operands_ready & dst_ready;
  // the accelerator interface stalled us
  assign acc_stall = (acc_qvalid_o & ~acc_qready_i);
  // the LSU Interface didn't accept our request yet
  assign lsu_stall = (lsu_qvalid & ~lsu_qready);
  // Stall the stage if we either didn't get a valid instruction or the LSU/Accelerator is not ready
  assign stall = ~valid_instr | lsu_stall | acc_stall;

  // --------------------
  // Instruction Frontend
  // --------------------
  assign consec_pc = pc_q + ((is_branch & alu_result[0]) ? bimm : 'd4);

  always_comb begin
    pc_d = pc_q;
    // if we got a valid instruction word increment the PC unless we are waiting for an event
    if (!stall && !wfi_q) begin
      casez (next_pc)
        Consec: pc_d = consec_pc;
        Alu: pc_d = alu_result & {{31{1'b1}}, ~zero_lsb};
        Exception: pc_d = MTVEC;
        MRet: pc_d = epc_q[M];
        SRet: pc_d = epc_q[S];
      endcase
    end
  end

  // --------------------
  // Decoder
  // --------------------
  assign rd = inst_data_i[7 + RegWidth - 1:7];
  assign rs1 = inst_data_i[15 + RegWidth - 1:15];
  assign rs2 = inst_data_i[20 + RegWidth - 1:20];

  always_comb begin
    illegal_inst = 1'b0;
    alu_op = Add;
    opa_select = None;
    opb_select = None;

    flush_i_valid_o = 1'b0;
    next_pc = Consec;

    rd_select = RdAlu;
    write_rd = 1'b1;
    // if we are writing the field this cycle we need
    // an int destination register
    uses_rd = write_rd;

    rd_bypass = '0;
    zero_lsb = 1'b0;
    is_branch = 1'b0;
    // LSU interface
    is_load = 1'b0;
    is_store = 1'b0;
    is_fp_load = 1'b0;
    is_fp_store = 1'b0;
    is_signed = 1'b0;
    ls_size = Byte;
    ls_amo = AMONone;

    acc_qvalid_o = 1'b0;
    acc_register_rd = 1'b0;

    csr_en = 1'b0;
    wfi_d = (wake_up_sync_i) ? 1'b0 : wfi_q;

    unique casez (inst_data_i)
      ADD: begin
        opa_select = Reg;
        opb_select = Reg;
      end
      ADDI: begin
        opa_select = Reg;
        opb_select = IImmediate;
      end
      SUB: begin
        alu_op = Sub;
        opa_select = Reg;
        opb_select = Reg;
      end
      XOR: begin
        opa_select = Reg;
        opb_select = Reg;
        alu_op = LXor;
      end
      XORI: begin
        alu_op = LXor;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      OR: begin
        opa_select = Reg;
        opb_select = Reg;
        alu_op = LOr;
      end
      ORI: begin
        alu_op = LOr;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      AND: begin
        alu_op = LAnd;
        opa_select = Reg;
        opb_select = Reg;
      end
      ANDI: begin
        alu_op = LAnd;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      SLT: begin
        alu_op = Slt;
        opa_select = Reg;
        opb_select = Reg;
      end
      SLTI: begin
        alu_op = Slt;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      SLTU: begin
        alu_op = Sltu;
        opa_select = Reg;
        opb_select = Reg;
      end
      SLTIU: begin
        alu_op = Sltu;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      SLL: begin
        alu_op = Sll;
        opa_select = Reg;
        opb_select = Reg;
      end
      SRL: begin
        alu_op = Srl;
        opa_select = Reg;
        opb_select = Reg;
      end
      SRA: begin
        alu_op = Sra;
        opa_select = Reg;
        opb_select = Reg;
      end
      SLLI: begin
        alu_op = Sll;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      SRLI: begin
        alu_op = Srl;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      SRAI: begin
        alu_op = Sra;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      LUI: begin
        opa_select = None;
        opb_select = None;
        rd_select = RdBypass;
        rd_bypass = uimm;
      end
      AUIPC: begin
        opa_select = UImmediate;
        opb_select = PC;
      end
      JAL: begin
        rd_select = RdConsecPC;
        opa_select = JImmediate;
        opb_select = PC;
        next_pc = Alu;
      end
      JALR: begin
        rd_select = RdConsecPC;
        opa_select = Reg;
        opb_select = IImmediate;
        next_pc = Alu;
        zero_lsb = 1'b1;
      end
      // use the ALU for comparisons
      BEQ: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        alu_op = Eq;
        opa_select = Reg;
        opb_select = Reg;
      end
      BNE: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        alu_op = Neq;
        opa_select = Reg;
        opb_select = Reg;
      end
      BLT: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        alu_op = Slt;
        opa_select = Reg;
        opb_select = Reg;
      end
      BLTU: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        alu_op = Sltu;
        opa_select = Reg;
        opb_select = Reg;
      end
      BGE: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        alu_op = Ge;
        opa_select = Reg;
        opb_select = Reg;
      end
      BGEU: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        alu_op = Geu;
        opa_select = Reg;
        opb_select = Reg;
      end
      // Load/Stores
      SB: begin
        write_rd = 1'b0;
        is_store = 1'b1;
        opa_select = Reg;
        opb_select = SImmediate;
      end
      SH: begin
        write_rd = 1'b0;
        is_store = 1'b1;
        ls_size = HalfWord;
        opa_select = Reg;
        opb_select = SImmediate;
      end
      SW: begin
        write_rd = 1'b0;
        is_store = 1'b1;
        ls_size = Word;
        opa_select = Reg;
        opb_select = SImmediate;
      end
      LB: begin
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      LH: begin
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = HalfWord;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      LW: begin
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      LBU: begin
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      LHU: begin
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        ls_size = HalfWord;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      // CSR Instructions
      CSRRW: begin // Atomic Read/Write CSR
        opa_select = Reg;
        opb_select = None;
        rd_select = RdBypass;
        rd_bypass = csr_rvalue;
        csr_en = 1'b1;
      end
      CSRRWI: begin
        opa_select = CSRImmmediate;
        opb_select = None;
        rd_select = RdBypass;
        rd_bypass = csr_rvalue;
        csr_en = 1'b1;
      end
      CSRRS: begin  // Atomic Read and Set Bits in CSR
          alu_op = LOr;
          opa_select = Reg;
          opb_select = CSR;
          rd_select = RdBypass;
          rd_bypass = csr_rvalue;
          csr_en = 1'b1;
      end
      CSRRSI: begin
        // offload CSR enable to FP SS
        if (inst_data_i[31:20] != snitch_cfg::CSR_SSR) begin
          alu_op = LOr;
          opa_select = CSRImmmediate;
          opb_select = CSR;
          rd_select = RdBypass;
          rd_bypass = csr_rvalue;
          csr_en = 1'b1;
        end else begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end
      end
      CSRRC: begin // Atomic Read and Clear Bits in CSR
        alu_op = LNAnd;
        opa_select = Reg;
        opb_select = CSR;
        rd_select = RdBypass;
        rd_bypass = csr_rvalue;
        csr_en = 1'b1;
      end
      CSRRCI: begin
        if (inst_data_i[31:20] != snitch_cfg::CSR_SSR) begin
          alu_op = LNAnd;
          opa_select = CSRImmmediate;
          opb_select = CSR;
          rd_select = RdBypass;
          rd_bypass = csr_rvalue;
          csr_en = 1'b1;
        end else begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end
      end
      ECALL,
      EBREAK: begin
        write_rd = 1'b0;
        uses_rd = 1'b0;
        next_pc = Exception;
      end
      // Environment return
      SRET: begin
        write_rd = 1'b0;
        if (priv_lvl_q inside {snitch_pkg::PrivLvlM, snitch_pkg::PrivLvlS}) next_pc = SRet;
        else illegal_inst = 1'b1;
      end
      MRET: begin
        write_rd = 1'b0;
        if (priv_lvl_q inside {snitch_pkg::PrivLvlM}) next_pc = MRet;
        else illegal_inst = 1'b1;
      end
      // Decode as NOP
      FENCE: begin
        write_rd = 1'b0;
      end
      FENCE_I: begin
        flush_i_valid_o = valid_instr;
      end
      WFI: begin
        wfi_d = ~stall;
      end
      // Atomics
      AMOADD_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOAdd;
        opa_select = Reg;
        opb_select = Reg;
      end
      AMOXOR_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOXor;
        opa_select = Reg;
        opb_select = Reg;
      end
      AMOOR_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOOr;
        opa_select = Reg;
        opb_select = Reg;
      end
      AMOAND_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOAnd;
        opa_select = Reg;
        opb_select = Reg;
      end
      AMOMIN_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOMinu;
        opa_select = Reg;
        opb_select = Reg;
      end
      AMOMAX_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOMax;
        opa_select = Reg;
        opb_select = Reg;
      end
      AMOMINU_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOMinu;
        opa_select = Reg;
        opb_select = Reg;
      end
      AMOMAXU_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOMaxu;
        opa_select = Reg;
        opb_select = Reg;
      end
      AMOSWAP_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOSwap;
        opa_select = Reg;
        opb_select = Reg;
      end
      LR_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOLR;
        opa_select = Reg;
        opb_select = Reg;
      end
      SC_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOSC;
        opa_select = Reg;
        opb_select = Reg;
      end
      // Off-load to shared multiplier
      MUL,
      MULH,
      MULHSU,
      MULHU,
      DIV,
      DIVU,
      REM,
      REMU,
      MULW,
      DIVW,
      DIVUW,
      REMW,
      REMUW: begin
        write_rd = 1'b0;
        uses_rd = 1'b1;
        acc_qvalid_o = valid_instr;
        opa_select = Reg;
        opb_select = Reg;
        acc_register_rd = 1'b1;
      end
      // Offload FP-FP Instructions - fire and forget
      // TODO (smach): Check legal rounding modes and issue illegal isn if needed
      // Single Precision Floating-Point
      FADD_S,
      FSUB_S,
      FMUL_S,
      FDIV_S,
      FSGNJ_S,
      FSGNJN_S,
      FSGNJX_S,
      FMIN_S,
      FMAX_S,
      FSQRT_S,
      FMADD_S,
      FMSUB_S,
      FNMSUB_S,
      FNMADD_S: begin
        if (RVFD && RVF) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      VFADD_S,
      VFADD_R_S,
      VFSUB_S,
      VFSUB_R_S,
      VFMUL_S,
      VFMUL_R_S,
      VFDIV_S,
      VFDIV_R_S,
      VFMIN_S,
      VFMIN_R_S,
      VFMAX_S,
      VFMAX_R_S,
      VFSQRT_S,
      VFMAC_S,
      VFMAC_R_S,
      VFMRE_S,
      VFMRE_R_S,
      VFSGNJ_S,
      VFSGNJ_R_S,
      VFSGNJN_S,
      VFSGNJN_R_S,
      VFSGNJX_S,
      VFSGNJX_R_S,
      VFCPKA_S_S,
      VFCPKA_S_D: begin
        if (RVFD && XFVEC && RVF && RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Double Precision Floating-Point
      FADD_D,
      FSUB_D,
      FMUL_D,
      FDIV_D,
      FSGNJ_D,
      FSGNJN_D,
      FSGNJX_D,
      FMIN_D,
      FMAX_D,
      FSQRT_D,
      FMADD_D,
      FMSUB_D,
      FNMSUB_D,
      FNMADD_D: begin
        if (RVFD && RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FCVT_S_D,
      FCVT_D_S: begin
        if (RVFD && RVF && RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // [Alt] Half Precision Floating-Point
      FADD_H,
      FSUB_H,
      FMUL_H,
      FDIV_H,
      FSQRT_H,
      FMADD_H,
      FMSUB_H,
      FNMSUB_H,
      FNMADD_H: begin
        if (RVFD && (XF16 && inst_data_i[14:12] inside {[3'b000:3'b100], 3'b111}) ||
            (XF16ALT && inst_data_i[14:12] == 3'b101)) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Half Precision Floating-Point
      FSGNJ_H,
      FSGNJN_H,
      FSGNJX_H,
      FMIN_H,
      FMAX_H: begin
        if (RVFD && XF16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FCVT_S_H,
      FCVT_H_S: begin
        if (RVFD && RVF) begin
          if ((XF16 && inst_data_i[14:12] inside {[3'b000:3'b100], 3'b111}) ||
              (XF16ALT && inst_data_i[14:12] == 3'b101)) begin
            write_rd = 1'b0;
            acc_qvalid_o = valid_instr;
          end else begin
            illegal_inst = 1'b1;
          end
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FCVT_D_H,
      FCVT_H_D: begin
        if (RVFD && RVD) begin
          if ((XF16 && inst_data_i[14:12] inside {[3'b000:3'b100], 3'b111}) ||
              (XF16ALT && inst_data_i[14:12] == 3'b101)) begin
            write_rd = 1'b0;
            acc_qvalid_o = valid_instr;
          end else begin
            illegal_inst = 1'b1;
          end
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      VFADD_H,
      VFADD_R_H,
      VFSUB_H,
      VFSUB_R_H,
      VFMUL_H,
      VFMUL_R_H,
      VFDIV_H,
      VFDIV_R_H,
      VFMIN_H,
      VFMIN_R_H,
      VFMAX_H,
      VFMAX_R_H,
      VFSQRT_H,
      VFMAC_H,
      VFMAC_R_H,
      VFMRE_H,
      VFMRE_R_H,
      VFSGNJ_H,
      VFSGNJ_R_H,
      VFSGNJN_H,
      VFSGNJN_R_H,
      VFSGNJX_H,
      VFSGNJX_R_H,
      VFCPKA_H_S: begin
        if (RVFD && XFVEC && XF16 && RVF) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      VFCVT_S_H,
      VFCVTU_S_H,
      VFCVT_H_S,
      VFCVTU_H_S,
      VFCPKB_H_S,
      VFCPKA_H_D,
      VFCPKB_H_D: begin
        if (RVFD && XFVEC && XF16 && RVF && RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Alternate Half Precision Floating-Point
      FSGNJ_AH,
      FSGNJN_AH,
      FSGNJX_AH,
      FMIN_AH,
      FMAX_AH: begin
        if (RVFD && XF16ALT) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FCVT_S_AH: begin
        if (RVFD && RVF && XF16ALT) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FCVT_D_AH: begin
        if (RVFD && RVD && XF16ALT) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FCVT_H_AH,
      FCVT_AH_H: begin
        if (RVFD && XF16 && XF16ALT) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      VFADD_AH,
      VFADD_R_AH,
      VFSUB_AH,
      VFSUB_R_AH,
      VFMUL_AH,
      VFMUL_R_AH,
      VFDIV_AH,
      VFDIV_R_AH,
      VFMIN_AH,
      VFMIN_R_AH,
      VFMAX_AH,
      VFMAX_R_AH,
      VFSQRT_AH,
      VFMAC_AH,
      VFMAC_R_AH,
      VFMRE_AH,
      VFMRE_R_AH,
      VFSGNJ_AH,
      VFSGNJ_R_AH,
      VFSGNJN_AH,
      VFSGNJN_R_AH,
      VFSGNJX_AH,
      VFSGNJX_R_AH,
      VFCPKA_AH_S: begin
        if (RVFD && XFVEC && XF16ALT && RVF) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      VFCVT_S_AH,
      VFCVTU_S_AH,
      VFCVT_AH_S,
      VFCVTU_AH_S,
      VFCPKB_AH_S,
      VFCPKA_AH_D,
      VFCPKB_AH_D: begin
        if (RVFD && XFVEC && XF16ALT && RVF && RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      VFCVT_H_AH,
      VFCVTU_H_AH,
      VFCVT_AH_H,
      VFCVTU_AH_H: begin
        if (RVFD && XFVEC && XF16ALT && XF16 && RVF) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Quarter Precision Floating-Point
      FADD_B,
      FSUB_B,
      FMUL_B,
      FDIV_B,
      FSGNJ_B,
      FSGNJN_B,
      FSGNJX_B,
      FMIN_B,
      FMAX_B,
      FSQRT_B,
      FMADD_B,
      FMSUB_B,
      FNMSUB_B,
      FNMADD_B: begin
        if (RVFD && XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FCVT_S_B,
      FCVT_B_S: begin
        if (RVFD && RVF && XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FCVT_D_B,
      FCVT_B_D: begin
        if (RVFD && RVD && XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FCVT_H_B,
      FCVT_B_H: begin
        if (RVFD && XF16 && XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FCVT_AH_B,
      FCVT_B_AH: begin
        if (RVFD && RVF && RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      VFADD_B,
      VFADD_R_B,
      VFSUB_B,
      VFSUB_R_B,
      VFMUL_B,
      VFMUL_R_B,
      VFDIV_B,
      VFDIV_R_B,
      VFMIN_B,
      VFMIN_R_B,
      VFMAX_B,
      VFMAX_R_B,
      VFSQRT_B,
      VFMAC_B,
      VFMAC_R_B,
      VFMRE_B,
      VFMRE_R_B,
      VFSGNJ_B,
      VFSGNJ_R_B,
      VFSGNJN_B,
      VFSGNJN_R_B,
      VFSGNJX_B,
      VFSGNJX_R_B: begin
        if (RVFD && XFVEC && XF8 && FLEN >= 16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      VFCPKA_B_S,
      VFCPKB_B_S: begin
        if (RVFD && XFVEC && XF8 && RVF) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      VFCVT_S_B,
      VFCVTU_S_B,
      VFCVT_B_S,
      VFCVTU_B_S: begin
        if (RVFD && XFVEC && XF8 && RVF && FLEN >= 64) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      VFCPKC_B_S,
      VFCPKD_B_S,
      VFCPKA_B_D,
      VFCPKB_B_D,
      VFCPKC_B_D,
      VFCPKD_B_D: begin
        if (RVFD && XFVEC && XF8 && RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      VFCVT_H_B,
      VFCVTU_H_B,
      VFCVT_B_H,
      VFCVTU_B_H: begin
        if (RVFD && XFVEC && XF8 && XF16 && FLEN >= 32) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      VFCVT_AH_B,
      VFCVTU_AH_B,
      VFCVT_B_AH,
      VFCVTU_B_AH: begin
        if (RVFD && XFVEC && XF8 && XF16ALT && FLEN >= 32) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Offload FP-Int Instructions - fire and forget
      // Single Precision Floating-Point
      FLE_S,
      FLT_S,
      FEQ_S,
      FCLASS_S,
      FCVT_W_S,
      FCVT_WU_S,
      FMV_X_W: begin
        if (RVFD && RVF) begin
          write_rd = 1'b0;
          uses_rd = 1'b1;
          acc_qvalid_o = valid_instr;
          acc_register_rd = 1'b1; // No RS in GPR but RD in GPR, register in int scoreboard
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      VFEQ_S,
      VFEQ_R_S,
      VFNE_S,
      VFNE_R_S,
      VFLT_S,
      VFLT_R_S,
      VFGE_S,
      VFGE_R_S,
      VFLE_S,
      VFLE_R_S,
      VFGT_S,
      VFGT_R_S,
      VFCLASS_S: begin
        if (RVFD && XFVEC && RVF && FLEN >= 64) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Double Precision Floating-Point
      FLE_D,
      FLT_D,
      FEQ_D,
      FCLASS_D,
      FCVT_W_D,
      FCVT_WU_D: begin
        if (RVFD && RVD) begin
          write_rd = 1'b0;
          uses_rd = 1'b1;
          acc_qvalid_o = valid_instr;
          acc_register_rd = 1'b1; // No RS in GPR but RD in GPR, register in int scoreboard
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Half Precision Floating-Point
      FLE_H,
      FLT_H,
      FEQ_H,
      FCLASS_H,
      FCVT_W_H,
      FCVT_WU_H,
      FMV_X_H: begin
        if (RVFD && (XF16 && inst_data_i[14:12] inside {[3'b000:3'b100], 3'b111}) ||
              (XF16ALT && inst_data_i[14:12] == 3'b101)) begin
          write_rd = 1'b0;
          uses_rd = 1'b1;
          acc_qvalid_o = valid_instr;
          acc_register_rd = 1'b1; // No RS in GPR but RD in GPR, register in int scoreboard
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      VFEQ_H,
      VFEQ_R_H,
      VFNE_H,
      VFNE_R_H,
      VFLT_H,
      VFLT_R_H,
      VFGE_H,
      VFGE_R_H,
      VFLE_H,
      VFLE_R_H,
      VFGT_H,
      VFGT_R_H,
      VFCLASS_H: begin
        if (RVFD && XFVEC && XF16 && FLEN >= 32) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      VFMV_X_H,
      VFCVT_X_H,
      VFCVT_XU_H: begin
        if (RVFD && XFVEC && XF16 && FLEN >= 32 && ~RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Alternate Half Precision Floating-Point
      FLE_AH,
      FLT_AH,
      FEQ_AH,
      FCLASS_AH,
      FMV_X_AH: begin
        if (RVFD && XF16ALT) begin
          write_rd = 1'b0;
          uses_rd = 1'b1;
          acc_qvalid_o = valid_instr;
          acc_register_rd = 1'b1; // No RS in GPR but RD in GPR, register in int scoreboard
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      VFEQ_AH,
      VFEQ_R_AH,
      VFNE_AH,
      VFNE_R_AH,
      VFLT_AH,
      VFLT_R_AH,
      VFGE_AH,
      VFGE_R_AH,
      VFLE_AH,
      VFLE_R_AH,
      VFGT_AH,
      VFGT_R_AH,
      VFCLASS_AH: begin
        if (RVFD && XFVEC && XF16ALT && FLEN >= 32) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      VFMV_X_AH,
      VFCVT_X_AH,
      VFCVT_XU_AH: begin
        if (RVFD && XFVEC && XF16ALT && FLEN >= 32 && ~RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Quarter Precision Floating-Point
      FLE_B,
      FLT_B,
      FEQ_B,
      FCLASS_B,
      FCVT_W_B,
      FCVT_WU_B,
      FMV_X_B: begin
        if (RVFD && XF8) begin
          write_rd = 1'b0;
          uses_rd = 1'b1;
          acc_qvalid_o = valid_instr;
          acc_register_rd = 1'b1; // No RS in GPR but RD in GPR, register in int scoreboard
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      VFEQ_B,
      VFEQ_R_B,
      VFNE_B,
      VFNE_R_B,
      VFLT_B,
      VFLT_R_B,
      VFGE_B,
      VFGE_R_B,
      VFLE_B,
      VFLE_R_B,
      VFGT_B,
      VFGT_R_B: begin
        if (RVFD && XFVEC && XF8 && FLEN >= 16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      VFMV_X_B,
      VFCLASS_B,
      VFCVT_X_B,
      VFCVT_XU_B: begin
        if (RVFD && XFVEC && XF8 && FLEN >= 16 && ~RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Offload Int-FP Instructions - fire and forget
      // Single Precision Floating-Point
      FMV_W_X,
      FCVT_S_W,
      FCVT_S_WU: begin
        if (RVFD && RVF) begin
          opa_select = Reg;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Double Precision Floating-Point
      FCVT_D_W,
      FCVT_D_WU: begin
        if (RVFD && RVD) begin
          opa_select = Reg;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Half Precision Floating-Point
      FMV_H_X,
      FCVT_H_W,
      FCVT_H_WU: begin
        if (RVFD && XF16) begin
          opa_select = Reg;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      VFMV_H_X,
      VFCVT_H_X,
      VFCVT_H_XU: begin
        if (RVFD && XFVEC && XF16 && FLEN >= 32 && ~RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Alternate Half Precision Floating-Point
      FMV_AH_X: begin
        if (RVFD && XF16ALT) begin
          opa_select = Reg;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      VFMV_AH_X,
      VFCVT_AH_X,
      VFCVT_AH_XU: begin
        if (RVFD && XFVEC && XF16ALT && FLEN >= 32 && ~RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Quarter Precision Floating-Point
      FMV_B_X,
      FCVT_B_W,
      FCVT_B_WU: begin
        if (RVFD && XF8) begin
          opa_select = Reg;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      VFMV_B_X,
      VFCVT_B_X,
      VFCVT_B_XU: begin
        if (RVFD && XFVEC && XF8 && FLEN >= 16 && ~RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // FP Sequencer
      FREP: begin
        if (RVFD && FP_PRESENT)
          opa_select = Reg;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
      end
      // Floating-Point Load/Store
      // Single Precision Floating-Point
      FLW: begin
        if (RVFD && RVF) begin
          opa_select = Reg;
          opb_select = IImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          ls_size = Word;
          is_fp_load = 1'b1;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FSW: begin
        if (RVFD && RVF) begin
          opa_select = Reg;
          opb_select = SFImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          ls_size = Word;
          is_fp_store = 1'b1;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Double Precision Floating-Point
      FLD: begin
        if (RVFD && (RVD || XFVEC)) begin
          opa_select = Reg;
          opb_select = IImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          ls_size = Double;
          is_fp_load = 1'b1;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FSD: begin
        if (RVFD && (RVD || XFVEC)) begin
          opa_select = Reg;
          opb_select = SFImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          ls_size = Double;
          is_fp_store = 1'b1;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Half Precision Floating-Point
      FLH: begin
        if (RVFD && (XF16 || XF16ALT)) begin
          opa_select = Reg;
          opb_select = IImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          ls_size = HalfWord;
          is_fp_load = 1'b1;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FSH: begin
        if (RVFD && (XF16 || XF16ALT)) begin
          opa_select = Reg;
          opb_select = SFImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          ls_size = HalfWord;
          is_fp_store = 1'b1;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Quarter Precision Floating-Point
      FLB: begin
        if (RVFD && XF8) begin
          opa_select = Reg;
          opb_select = IImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          ls_size = Byte;
          is_fp_load = 1'b1;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      FSB: begin
        if (RVFD && XF8) begin
          opa_select = Reg;
          opb_select = SFImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          ls_size = Byte;
          is_fp_store = 1'b1;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // DMA instructions
      riscv_instr::DM_SRC,
      riscv_instr::DM_DST,
      riscv_instr::DM_TWOD_STRD : begin
        if (SDMA) begin
          opa_select   = Reg;
          opb_select   = Reg;
          acc_qvalid_o = valid_instr;
          write_rd     = 1'b0;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::DM_STRTI : begin
        if (SDMA) begin
          opa_select      = Reg;
          acc_qvalid_o    = valid_instr;
          write_rd        = 1'b0;
          uses_rd         = 1'b1;
          acc_register_rd = 1'b1;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::DM_STRT : begin
        if (SDMA) begin
          opa_select      = Reg;
          opb_select      = Reg;
          acc_qvalid_o    = valid_instr;
          write_rd        = 1'b0;
          uses_rd         = 1'b1;
          acc_register_rd = 1'b1;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::DM_STATI,
      riscv_instr::DM_ERRI : begin
        if (SDMA) begin
          acc_qvalid_o    = valid_instr;
          write_rd        = 1'b0;
          uses_rd         = 1'b1;
          acc_register_rd = 1'b1;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::DM_STAT,
      riscv_instr::DM_ERR : begin
        if (SDMA) begin
          opa_select      = Reg;
          acc_qvalid_o    = valid_instr;
          write_rd        = 1'b0;
          uses_rd         = 1'b1;
          acc_register_rd = 1'b1;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::DM_TWOD_REPS : begin
        if (SDMA) begin
          opa_select      = Reg;
          acc_qvalid_o    = valid_instr;
          write_rd        = 1'b0;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Offload Multiply Instructions
      // TODO(zarubaf): Illegal Instructions
      default: begin
        illegal_inst = 1'b1;
      end
    endcase

    // Sanitize illegal instructions so that they don't exert any side-effects.
    if (exception) begin
     write_rd = 1'b0;
     uses_rd = 1'b0;
     acc_qvalid_o = 1'b0;
     next_pc = Exception;
    end
  end

  assign exception = illegal_inst | ld_addr_misaligned | st_addr_misaligned | illegal_csr;

  // pragma translate_off
  always_ff @(posedge clk_i) begin
    if (!rst_i && illegal_inst && inst_valid_o && inst_ready_i) begin
      $display("[Illegal Instruction Core %0d] PC: %h Data: %h", hart_id_i, inst_addr_o, inst_data_i);
    end
  end
  // pragma translate_on

  // CSR logic
  always_comb begin
    csr_rvalue = '0;
    illegal_csr = '0;
    priv_lvl_d = priv_lvl_q;
    // registers
    fcsr_d = fcsr_q;
    fcsr_d.fflags = fcsr_q.fflags | fpu_status_i;
    scratch_d = scratch_q;
    epc_d = epc_q;
    cause_d = cause_q;
    satp_d = satp_q;
    mseg_d = mseg_q;
    mpp_d = mpp_q;
    spp_d = spp_q;

    if (csr_en) begin
      // Check privilege level.
      if ((priv_lvl_q & inst_data_i[29:28]) == inst_data_i[29:28]) begin
        unique case (inst_data_i[31:20])
          CSR_MISA: csr_rvalue = (1   <<  0)          // A - Atomic Instructions extension
                               | (0   <<  2)          // C - Compressed extension
                               | ((RVFD & RVD) <<  3) // D - Double precsision floating-point extension
                               | ((RVFD & RVE) <<  4) // E - RV32E base ISA
                               | ((RVFD & RVF) <<  5) // F - Single precsision floating-point extension
                               | (1   <<  8)          // I - RV32I/64I/128I base ISA
                               | (1   << 12)          // M - Integer Multiply/Divide extension
                               | (0   << 13)          // N - User level interrupts supported
                               | (0   << 18)          // S - Supervisor mode implemented
                               | (0   << 20)          // U - User mode implemented
                               | (((NSX & RVFD) | SDMA) << 23)  // X - Non-standard extensions present
                               | (1   << 30);         // RV32
          CSR_MHARTID: begin
            csr_rvalue = hart_id_i;
          end
          `ifdef SNITCH_ENABLE_PERF
          CSR_MCYCLE: begin
            csr_rvalue = cycle_q[31:0];
          end
          CSR_MINSTRET: begin
            csr_rvalue = instret_q[31:0];
          end
          CSR_MCYCLEH: begin
            csr_rvalue = cycle_q[63:32];
          end
          CSR_MINSTRETH: begin
            csr_rvalue = instret_q[63:32];
          end
          `endif
          snitch_cfg::CSR_MSEG: begin
            csr_rvalue = mseg_q;
            mseg_d = alu_result[$bits(mseg_q)-1:0];
          end
          // Privleged Extension:
          CSR_MSTATUS: begin
            automatic snitch_pkg::status_rv32_t mstatus, mstatus_d;
            mstatus = '0;
            if (RVFD) begin
              mstatus.fs = snitch_pkg::XDirty;
              mstatus.sd = 1'b1;
            end
            mstatus.mpp = mpp_q;
            mstatus.spp = spp_q;
            csr_rvalue = mstatus;
            mstatus_d = snitch_pkg::status_rv32_t'(alu_result);
            mpp_d = mstatus_d.mpp;
            spp_d = mstatus_d.spp;
          end
          CSR_MEPC: begin
            csr_rvalue = epc_q[M];
            epc_d[M] = alu_result[31:0];
          end
          CSR_MCAUSE: begin
            csr_rvalue = cause_q[M];
            cause_d[M] = alu_result[3:0];
          end
          CSR_MTVAL:; // tied-off
          CSR_MTVEC: csr_rvalue = MTVEC;
          CSR_MSCRATCH: begin
            csr_rvalue = scratch_q[M];
            scratch_d[M] = alu_result[31:0];
          end
          CSR_MEDELEG:; // we currently don't support delegation
          CSR_SSTATUS: begin
            automatic snitch_pkg::status_rv32_t mstatus;
            mstatus = '0;
            mstatus.spp = spp_q;
            csr_rvalue = mstatus;
            spp_d = mstatus.spp;
          end
          CSR_SSCRATCH: begin
            csr_rvalue = scratch_q[S];
            scratch_d[S] = alu_result[31:0];
          end
          CSR_SEPC: begin
            csr_rvalue = epc_q[S];
            epc_d[S] = alu_result[31:0];
          end
          CSR_SCAUSE: begin
            csr_rvalue = cause_q[S];
            cause_d[S] = alu_result[3:0];
          end
          CSR_STVAL:; // tied-off
          CSR_STVEC: csr_rvalue = STVEC;
          CSR_SATP: begin
            csr_rvalue = satp_q;
            satp_d.ppn = alu_result[21:0];
            satp_d.mode = alu_result[31];
          end
          // F/D Extension
          CSR_FFLAGS: begin
            if (RVFD) begin
              csr_rvalue = {27'b0, fcsr_q.fflags};
              fcsr_d.fflags = fpnew_pkg::status_t'(alu_result[4:0]);
            end else illegal_csr = 1'b1;
          end
          CSR_FRM: begin
            if (RVFD) begin
              csr_rvalue = {29'b0, fcsr_q.frm};
              fcsr_d.frm = fpnew_pkg::roundmode_e'(alu_result[2:0]);
            end else illegal_csr = 1'b1;
          end
          CSR_FCSR: begin
            if (RVFD) begin
              csr_rvalue = {24'b0, fcsr_q};
              fcsr_d = fcsr_t'(alu_result[7:0]);
            end else illegal_csr = 1'b1;
          end
          default: csr_rvalue = '0;
        endcase
      end else illegal_csr = 1'b1;
    end

    // Manipulate CSRs / Privilege Stack
    if (valid_instr) begin
      // Exceptions
      // Illegal Instructions.
      if (illegal_inst || illegal_csr) begin
        cause_d = snitch_pkg::ILLEGAL_INSTR;
        epc_d[M] = pc_q;
        priv_lvl_d = snitch_pkg::PrivLvlM;
      end
      // Environment Calls.
      if (inst_data_i == riscv_instr::ECALL) begin
        unique case (priv_lvl_q)
          snitch_pkg::PrivLvlM: cause_d = snitch_pkg::ENV_CALL_MMODE;
          snitch_pkg::PrivLvlS: cause_d = snitch_pkg::ENV_CALL_SMODE;
          snitch_pkg::PrivLvlU: cause_d = snitch_pkg::ENV_CALL_UMODE;
          default: cause_d = snitch_pkg::ENV_CALL_MMODE;
        endcase
        epc_d[M] = pc_q;
        priv_lvl_d = snitch_pkg::PrivLvlM;
      end
      // Return from Environment.
      if (inst_data_i == riscv_instr::MRET) begin
        priv_lvl_d = mpp_q;
        mpp_d = snitch_pkg::PrivLvlU; // set default back to U-Mode
      end

      if (inst_data_i == riscv_instr::SRET) begin
        priv_lvl_d = snitch_pkg::priv_lvl_t'({1'b0, spp_q});
        spp_d = 1'b0;
      end
    end
  end

  snitch_regfile #(
    .DATA_WIDTH     ( 32       ),
    .NR_READ_PORTS  ( 2        ),
    .NR_WRITE_PORTS ( 1        ),
    .ZERO_REG_ZERO  ( 1        ),
    .ADDR_WIDTH     ( RegWidth )
  ) i_snitch_regfile (
    .clk_i,
    .raddr_i   ( gpr_raddr ),
    .rdata_o   ( gpr_rdata ),
    .waddr_i   ( gpr_waddr ),
    .wdata_i   ( gpr_wdata ),
    .we_i      ( gpr_we    )
  );

  // --------------------
  // Operand Select
  // --------------------
  always_comb begin
    unique case (opa_select)
      None: opa = '0;
      Reg: opa = gpr_rdata[0];
      UImmediate: opa = uimm;
      JImmediate: opa = jimm;
      CSRImmmediate: opa = {{{32-RegWidth}{1'b0}}, rs1};
      default: opa = '0;
    endcase
  end

  always_comb begin
    unique case (opb_select)
      None: opb = '0;
      Reg: opb = gpr_rdata[1];
      IImmediate: opb = iimm;
      SFImmediate, SImmediate: opb = simm;
      PC: opb = pc_q;
      CSR: opb = csr_rvalue;
      default: opb = '0;
    endcase
  end

  assign gpr_raddr[0] = rs1;
  assign gpr_raddr[1] = rs2;

  // --------------------
  // ALU
  // --------------------
  // Main Shifter
  logic [31:0] shift_opa, shift_opa_reversed;
  logic [31:0] shift_right_result, shift_left_result;
  logic [32:0] shift_opa_ext, shift_right_result_ext;
  logic shift_left, shift_arithmetic; // shift control
  for (genvar i = 0; i < 32; i++) begin : gen_reverse_opa
    assign shift_opa_reversed[i] = opa[31-i];
    assign shift_left_result[i] = shift_right_result[31-i];
  end
  assign shift_opa = shift_left ? shift_opa_reversed : opa;
  assign shift_opa_ext = {shift_opa[31] & shift_arithmetic, shift_opa};
  assign shift_right_result_ext = $unsigned($signed(shift_opa_ext) >>> opb[4:0]);
  assign shift_right_result = shift_right_result_ext[31:0];

  // Main Adder
  logic [32:0] alu_opa, alu_opb;
  assign adder_result = alu_opa + alu_opb;

  // ALU
  /* verilator lint_off WIDTH */
  always_comb begin
    alu_opa = $signed(opa);
    alu_opb = $signed(opb);

    alu_result = adder_result[31:0];
    shift_left = 1'b0;
    shift_arithmetic = 1'b0;

    unique case (alu_op)
      Sub: alu_opb = -$signed(opb);
      Slt: begin
        alu_opb = -$signed(opb);
        alu_result = {30'b0, adder_result[32]};
      end
      Ge: begin
        alu_opb = -$signed(opb);
        alu_result = {30'b0, ~adder_result[32]};
      end
      Sltu: begin
        alu_opa = $unsigned(opa);
        alu_opb = -$unsigned(opb);
        alu_result = {30'b0, adder_result[32]};
      end
      Geu: begin
        alu_opa = $unsigned(opa);
        alu_opb = -$unsigned(opb);
        alu_result = {30'b0, ~adder_result[32]};
      end
      Sll: begin
        shift_left = 1'b1;
        alu_result = shift_left_result;
      end
      Srl: alu_result = shift_right_result;
      Sra: begin
        shift_arithmetic = 1'b1;
        alu_result = shift_right_result;
      end
      LXor: alu_result = opa ^ opb;
      LAnd: alu_result = opa & opb;
      LNAnd: alu_result = (~opa) & opb;
      LOr: alu_result = opa | opb;
      Eq: begin
        alu_opb = -$signed(opb);
        alu_result = ~|adder_result;
      end
      Neq: begin
        alu_opb = -$signed(opb);
        alu_result = |adder_result;
      end
      BypassA: begin
        alu_result = opa;
      end
      default: alu_result = adder_result[31:0];
    endcase
  end
  /* verilator lint_on WIDTH */

  // --------------------
  // LSU
  // --------------------
  snitch_lsu #(
    .tag_t               ( logic[RegWidth-1:0]                ),
    .NumOutstandingLoads ( snitch_cfg::NumIntOutstandingLoads )
  ) i_snitch_lsu (
    .clk_i                                ,
    .rst_i                                ,
    .lsu_qtag_i   ( rd                    ),
    .lsu_qwrite   ( is_store              ),
    .lsu_qsigned  ( is_signed             ),
    .lsu_qaddr_i  ( {mseg_q, alu_result}  ),
    .lsu_qdata_i  ( {32'b0, gpr_rdata[1]} ),
    .lsu_qsize_i  ( ls_size               ),
    .lsu_qamo_i   ( ls_amo                ),
    .lsu_qvalid_i ( lsu_qvalid            ),
    .lsu_qready_o ( lsu_qready            ),
    .lsu_pdata_o  ( ld_result             ),
    .lsu_ptag_o   ( lsu_rd                ),
    .lsu_perror_o (                       ), // ignored for the moment
    .lsu_pvalid_o ( lsu_pvalid            ),
    .lsu_pready_i ( lsu_pready            ),
    .data_qaddr_o                          ,
    .data_qwrite_o                         ,
    .data_qdata_o                          ,
    .data_qsize_o                          ,
    .data_qamo_o                           ,
    .data_qstrb_o                          ,
    .data_qvalid_o                         ,
    .data_qready_i                         ,
    .data_pdata_i                          ,
    .data_perror_i                         ,
    .data_pvalid_i                         ,
    .data_pready_o
  );

  assign lsu_qvalid = valid_instr & (is_load | is_store) & ~(ld_addr_misaligned | st_addr_misaligned);

  // we can retire if we are not stalling and if the instruction is writing a register
  assign retire_i = write_rd & valid_instr & (rd != 0);

  // -----------------------
  // Unaligned Address Check
  // -----------------------
  always_comb begin
    ls_misaligned = 1'b0;
    unique case (ls_size)
      HalfWord: if (alu_result[0] != 1'b0) ls_misaligned = 1'b1;
      Word: if (alu_result[1:0] != 2'b00) ls_misaligned = 1'b1;
      Double: if (alu_result[2:0] != 3'b000) ls_misaligned = 1'b1;
      default: ls_misaligned = 1'b0;
    endcase
  end

  assign st_addr_misaligned = ls_misaligned & (is_store | is_fp_store);
  assign ld_addr_misaligned = ls_misaligned & (is_load | is_fp_load);

  // pragma translate_off
  always_ff @(posedge clk_i) begin
    if (!rst_i && (ld_addr_misaligned || st_addr_misaligned) && inst_valid_o && inst_ready_i) begin
      $display("[Misaligned Load/Store Core %0d] PC: %h Data: %h", hart_id_i, inst_addr_o, inst_data_i);
    end
  end
  // pragma translate_on

  // --------------------
  // Write-Back
  // --------------------
  // Write-back data, can come from:
  // 1. ALU/Jump Target/Bypass
  // 2. LSU
  // 3. Accelerator Bus
  logic [31:0] alu_writeback;
  always_comb begin
    casez (rd_select)
      RdAlu: alu_writeback = alu_result;
      RdConsecPC: alu_writeback = consec_pc;
      RdBypass: alu_writeback = rd_bypass;
      default: alu_writeback = alu_result;
    endcase
  end

  always_comb begin
    gpr_we[0] = 1'b0;
    gpr_waddr[0] = rd;
    gpr_wdata[0] = alu_writeback;
    // external interfaces
    lsu_pready = 1'b0;
    acc_pready_o = 1'b0;
    retire_acc = 1'b0;
    retire_load = 1'b0;

    if (retire_i) begin
      gpr_we[0] = 1'b1;
    // if we are not retiring another instruction retire the load now
    end else if (lsu_pvalid) begin
      retire_load = 1'b1;
      gpr_we[0] = 1'b1;
      gpr_waddr[0] = lsu_rd;
      gpr_wdata[0] = ld_result[31:0];
      lsu_pready = 1'b1;
    end else if (acc_pvalid_i) begin
      retire_acc = 1'b1;
      gpr_we[0] = 1'b1;
      gpr_waddr[0] = acc_pid_i;
      gpr_wdata[0] = acc_pdata_i[31:0];
      acc_pready_o = 1'b1;
    end
  end

  // --------------------------
  // RISC-V Formal Interface
  // --------------------------
  `ifdef RISCV_FORMAL
    logic instr_addr_misaligned;
    logic ld_addr_misaligned_q;
    // check that the instruction is a control transfer instruction
    assign instr_addr_misaligned = (inst_data_i inside {
      JAL,
      JALR,
      BEQ,
      BNE,
      BLT,
      BLTU,
      BGE,
      BGEU
    }) && (pc_d[1:0] != 2'b0);


    // retire an instruction and increase ordering bit
    `FFLSR(rvfi_order[0], rvfi_order[0] + 1, rvfi_valid[0], '0, clk_i, rst_i)

    logic [31:0] ld_instr_q;
    logic [31:0] ld_addr_q;
    logic [4:0]  rs1_q;
    logic [31:0] rs1_data_q;
    logic [31:0] pc_qq;
    // we need to latch the load
    `FFLSR(ld_instr_q, inst_data_i, latch_load, '0, clk_i, rst_i)
    `FFLSR(ld_addr_q, data_qaddr_o, latch_load, '0, clk_i, rst_i)
    `FFLSR(rs1_q, rs1, latch_load, '0, clk_i, rst_i)
    `FFLSR(rs1_data_q, gpr_rdata[0], latch_load, '0, clk_i, rst_i)
    `FFLSR(pc_qq, pc_d, latch_load, '0, clk_i, rst_i)
    `FFLSR(ld_addr_misaligned_q, ld_addr_misaligned, latch_load, '0, clk_i, rst_i)

    // in case we don't retire another instruction on port 1 we can use it for loads
    logic retire_load_port1;

    assign retire_load_port1 = retire_load & stall;
    // NRET: 1
    assign rvfi_halt[0] = 1'b0;
    assign rvfi_mode[0] = 2'b11;
    assign rvfi_intr[0] = 1'b0;
    assign rvfi_valid[0] = !stall | retire_load;
    assign rvfi_insn[0] = retire_load_port1 ? ld_instr_q : (is_load ? '0 : inst_data_i);
    assign rvfi_trap[0] = retire_load_port1 ? ld_addr_misaligned_q : illegal_inst
                                                                   | instr_addr_misaligned
                                                                   | st_addr_misaligned;
    assign rvfi_rs1_addr[0]  = (retire_load_port1) ? rs1_q : rs1;
    assign rvfi_rs1_rdata[0] = (retire_load_port1) ? rs1_data_q : gpr_rdata[0];
    assign rvfi_rs2_addr[0]  = (retire_load_port1) ? '0 : rs2;
    assign rvfi_rs2_rdata[0] = (retire_load_port1) ? '0 : gpr_rdata[1];
    assign rvfi_rd_addr[0]   = (retire_load_port1) ? lsu_rd : ((gpr_we[0] && write_rd) ? rd : '0);
    assign rvfi_rd_wdata[0]  = (retire_load_port1) ? (lsu_rd != 0 ? ld_result[31:0] : '0) : (rd != 0 && gpr_we[0] && write_rd) ? gpr_wdata[0] : 0;
    assign rvfi_pc_rdata[0]  = (retire_load_port1) ? pc_qq : pc_q;
    assign rvfi_pc_wdata[0]  = (retire_load_port1) ? (pc_qq + 4) : pc_d;
    assign rvfi_mem_addr[0]  = (retire_load_port1) ? ld_addr_q : data_qaddr_o;
    assign rvfi_mem_wmask[0] = (retire_load_port1) ? '0 : ((data_qvalid_o && data_qready_i) ? data_qstrb_o[3:0] : '0);
    assign rvfi_mem_rmask[0] = (retire_load_port1) ? 4'hf : '0;
    assign rvfi_mem_rdata[0] = (retire_load_port1) ? data_pdata_i[31:0] : '0;
    assign rvfi_mem_wdata[0] = (retire_load_port1) ? '0 : data_qdata_o[31:0];
  `endif
endmodule