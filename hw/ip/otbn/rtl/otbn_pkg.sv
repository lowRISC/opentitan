// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

package otbn_pkg;

  // Global Constants ==============================================================================

  // Data path width for BN (wide) instructions, in bits.
  parameter int WLEN = 256;

  // Number of 32-bit words per WLEN
  parameter int BaseWordsPerWLEN = WLEN / 32;

  // Number of flag groups
  parameter int NFlagGroups = 2;

  // Width of the GPR index/address
  parameter int GprAw = 5;

  // Number of General Purpose Registers (GPRs)
  parameter int NGpr = 2 ** GprAw;

  // Width of the WDR index/address
  parameter int WdrAw = 5;

  // Number of Wide Data Registers (WDRs)
  parameter int NWdr = 2 ** WdrAw;

  // Width of entropy input
  parameter int EdnDataWidth = 256;


  // Toplevel constants ============================================================================

  parameter int AlertFatal = 0;
  parameter int AlertRecov = 1;

  // Register file implementation selection enum.
  typedef enum integer {
    RegFileFF    = 0, // Generic flip-flop based implementation
    RegFileFPGA  = 1  // FPGA implmentation, does infer RAM primitives.
  } regfile_e;

  // Error bits
  //
  // Note: These errors are duplicated in the register HJSON (../data/otbn.hjson), the ISS
  // (../dv/otbnsim/sim/alert.py), and the DIF. If updating them here, update those too.
  typedef struct packed {
    logic fatal_reg;
    logic fatal_dmem;
    logic fatal_imem;
    logic loop;
    logic illegal_insn;
    logic call_stack;
    logic bad_insn_addr;
    logic bad_data_addr;
  } err_bits_t;

  // Constants =====================================================================================

  typedef enum logic {
    InsnSubsetBase = 1'b0,  // Base (RV32/Narrow) Instruction Subset
    InsnSubsetBignum = 1'b1 // Big Number (BN/Wide) Instruction Subset
  } insn_subset_e;

  // Opcodes (field [6:0] in the instruction), matching the RISC-V specification for the base
  // instruction subset.
  typedef enum logic [6:0] {
    InsnOpcodeBaseLoad       = 7'h03,
    InsnOpcodeBaseMemMisc    = 7'h0f,
    InsnOpcodeBaseOpImm      = 7'h13,
    InsnOpcodeBaseAuipc      = 7'h17,
    InsnOpcodeBaseStore      = 7'h23,
    InsnOpcodeBaseOp         = 7'h33,
    InsnOpcodeBaseLui        = 7'h37,
    InsnOpcodeBaseBranch     = 7'h63,
    InsnOpcodeBaseJalr       = 7'h67,
    InsnOpcodeBaseJal        = 7'h6f,
    InsnOpcodeBaseSystem     = 7'h73,
    InsnOpcodeBignumMisc     = 7'h0B,
    InsnOpcodeBignumArith    = 7'h2B,
    InsnOpcodeBignumMulqacc  = 7'h3B,
    InsnOpcodeBignumBaseMisc = 7'h7B
  } insn_opcode_e;

  typedef enum logic [3:0] {
    AluOpBaseAdd,
    AluOpBaseSub,

    AluOpBaseXor,
    AluOpBaseOr,
    AluOpBaseAnd,
    AluOpBaseNot,

    AluOpBaseSra,
    AluOpBaseSrl,
    AluOpBaseSll
  } alu_op_base_e;

  // TODO: Can we arrange this to simplify decoding logic?
  typedef enum logic [3:0] {
    AluOpBignumAdd,
    AluOpBignumAddc,
    AluOpBignumAddm,

    AluOpBignumSub,
    AluOpBignumSubb,
    AluOpBignumSubm,

    AluOpBignumRshi,

    AluOpBignumXor,
    AluOpBignumOr,
    AluOpBignumAnd,
    AluOpBignumNot,

    AluOpBignumSel,
    AluOpBignumMov
  } alu_op_bignum_e;

  typedef enum logic {
    ComparisonOpBaseEq,
    ComparisonOpBaseNeq
  } comparison_op_base_e;

  // Operand a source selection
  typedef enum logic [1:0] {
    OpASelRegister  = 'd0,
    OpASelZero = 'd1,
    OpASelCurrPc = 'd2
  } op_a_sel_e;

  // Operand b source selection
  typedef enum logic {
    OpBSelRegister  = 'd0,
    OpBSelImmediate = 'd1
  } op_b_sel_e;

  // Immediate b selection for base ISA
  typedef enum logic [2:0] {
    ImmBaseBI,
    ImmBaseBS,
    ImmBaseBB,
    ImmBaseBU,
    ImmBaseBJ,
    ImmBaseBL,
    ImmBaseBX
  } imm_b_sel_base_e;

  // Shift amount select for bignum ISA
  typedef enum logic [1:0] {
    ShamtSelBignumA,
    ShamtSelBignumS,
    ShamtSelBignumZero
  } shamt_sel_bignum_e;

  // Regfile write data selection
  typedef enum logic [2:0] {
    RfWdSelEx,
    RfWdSelNextPc,
    RfWdSelLsu,
    RfWdSelIspr,
    RfWdSelIncr,
    RfWdSelMac
  } rf_wd_sel_e;

  // Control and Status Registers (CSRs)
  parameter int CsrNumWidth = 12;
  typedef enum logic [CsrNumWidth-1:0] {
    CsrFg0   = 12'h7C0,
    CsrFg1   = 12'h7C1,
    CsrFlags = 12'h7C8,
    CsrMod0  = 12'h7D0,
    CsrMod1  = 12'h7D1,
    CsrMod2  = 12'h7D2,
    CsrMod3  = 12'h7D3,
    CsrMod4  = 12'h7D4,
    CsrMod5  = 12'h7D5,
    CsrMod6  = 12'h7D6,
    CsrMod7  = 12'h7D7,
    CsrRnd   = 12'hFC0
  } csr_e;

  // Wide Special Purpose Registers (WSRs)
  parameter int NWsr = 3; // Number of WSRs
  parameter int WsrNumWidth = $clog2(NWsr);
  typedef enum logic [WsrNumWidth-1:0] {
    WsrMod   = 'd0,
    WsrRnd   = 'd1,
    WsrAcc   = 'd2
  } wsr_e;

  // Internal Special Purpose Registers (ISPRs)
  // CSRs and WSRs have some overlap into what they map into. ISPRs are the actual registers in the
  // design which CSRs and WSRs are mapped on to.
  parameter int NIspr = NWsr + 1;
  parameter int IsprNumWidth = $clog2(NIspr);
  typedef enum logic [IsprNumWidth-1:0] {
    IsprMod   = 'd0,
    IsprRnd   = 'd1,
    IsprAcc   = 'd2,
    IsprFlags = 'd3
  } ispr_e;

  typedef logic [$clog2(NFlagGroups)-1:0] flag_group_t;

  typedef struct packed {
    logic Z;
    logic L;
    logic M;
    logic C;
  } flags_t;

  localparam int FlagsWidth = $bits(flags_t);

  typedef enum logic [$clog2(FlagsWidth)-1:0] {
    FlagC = 'd0,
    FlagM = 'd1,
    FlagL = 'd2,
    FlagZ = 'd3
  } flag_e;

  // TODO: Figure out how to add assertions for the enum type width; initial blocks, as produced by
  // ASSERT_INIT, aren't allowed in packages.
  //`ASSERT_INIT(WsrESizeMatchesParameter_A, $bits(wsr_e) == WsrNumWidth)

  // Structures for decoded instructions, grouped into three:
  // - insn_dec_shared_t - Anything that applies to both bignum and base microarchitecture
  // - insn_dec_base_t - Anything that only applies to the base side microarchitecture
  // - insn_dec_bignum_t - Anything that only applies to bignum side microarchitecture
  //
  // TODO: The variable names are rather short, especially "i" is confusing. Think about renaming.
  //
  typedef struct packed {
    insn_subset_e   subset;
    logic           ecall_insn;
    logic           ld_insn;
    logic           st_insn;
    logic           branch_insn;
    logic           jump_insn;
    logic           loop_insn;
    logic           ispr_rd_insn;
    logic           ispr_wr_insn;
    logic           ispr_rs_insn;
  } insn_dec_shared_t;

  typedef struct packed {
    logic [4:0]          d;             // Destination register
    logic [4:0]          a;             // First source register
    logic [4:0]          b;             // Second source register
    logic [31:0]         i;             // Immediate
    alu_op_base_e        alu_op;
    comparison_op_base_e comparison_op;
    op_a_sel_e           op_a_sel;
    op_b_sel_e           op_b_sel;
    logic                rf_ren_a;
    logic                rf_ren_b;
    logic                rf_we;
    rf_wd_sel_e          rf_wdata_sel;
    logic [11:0]         loop_bodysize;
    logic                loop_immediate;
  } insn_dec_base_t;

  typedef struct packed {
    logic [WdrAw-1:0]        d;           // Destination register
    logic [WdrAw-1:0]        a;           // First source register
    logic [WdrAw-1:0]        b;           // Second source register
    logic [WLEN-1:0]         i;           // Immediate

    logic                    rf_a_indirect; // Indirect lookup, bignum register index a comes from
                                            // base register a read
    logic                    rf_b_indirect; // Indirect lookup, bignum register index b comes from
                                            // base register b read
    logic                    rf_d_indirect; // Indirect lookup, bignum register index d comes from
                                            // base register b read using d in this struct

    logic                    d_inc;           // Increment destination register index in base
                                              // register file
    logic                    a_inc;           // Increment source register index a in base register
                                              // file
    logic                    a_wlen_word_inc; // Increment source register a in base register file
                                              // by WLEN word size
    logic                    b_inc;           // Increment source register index b in base register
                                              // file

    // Shifting only applies to a subset of ALU operations
    logic [$clog2(WLEN)-1:0] alu_shift_amt;   // Shift amount
    logic                    alu_shift_right; // Shift right if set otherwise left

    flag_group_t             alu_flag_group;
    flag_e                   alu_sel_flag;
    logic                    alu_flag_en;
    logic                    mac_flag_en;
    alu_op_bignum_e          alu_op;
    op_b_sel_e               alu_op_b_sel;

    logic [1:0]              mac_op_a_qw_sel;
    logic [1:0]              mac_op_b_qw_sel;
    logic                    mac_wr_hw_sel_upper;
    logic [1:0]              mac_pre_acc_shift;
    logic                    mac_zero_acc;
    logic                    mac_shift_out;
    logic                    mac_en;

    logic                    rf_we;
    rf_wd_sel_e              rf_wdata_sel;
    logic                    rf_ren_a;
    logic                    rf_ren_b;
  } insn_dec_bignum_t;

  typedef struct packed {
    alu_op_base_e     op;
    logic [31:0] operand_a;
    logic [31:0] operand_b;
  } alu_base_operation_t;

  typedef struct packed {
    comparison_op_base_e op;
    logic [31:0] operand_a;
    logic [31:0] operand_b;
  } alu_base_comparison_t;

  typedef struct packed {
    alu_op_bignum_e op;
    logic [WLEN-1:0]         operand_a;
    logic [WLEN-1:0]         operand_b;
    logic                    shift_right;
    logic [$clog2(WLEN)-1:0] shift_amt;
    flag_group_t             flag_group;
    flag_e                   sel_flag;
    logic                    alu_flag_en;
    logic                    mac_flag_en;
  } alu_bignum_operation_t;

  typedef struct packed {
    logic [WLEN-1:0] operand_a;
    logic [WLEN-1:0] operand_b;
    logic [1:0]      operand_a_qw_sel;
    logic [1:0]      operand_b_qw_sel;
    logic            wr_hw_sel_upper;
    logic [1:0]      pre_acc_shift_imm;
    logic            zero_acc;
    logic            shift_acc;
  } mac_bignum_operation_t;

  // States for controller state machine
  typedef enum logic [1:0] {
    OtbnStateHalt,
    OtbnStateRun,
    OtbnStateStall
  } otbn_state_e;

endpackage
