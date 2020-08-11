// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

package otbn_pkg;

  // Global Constants ==============================================================================

  // Data path width for BN (wide) instructions, in bits.
  parameter int WLEN = 256;

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


  // Toplevel constants ============================================================================

  // Alerts
  parameter int NumAlerts = 3;
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}};

  parameter int AlertImemUncorrectable = 0;
  parameter int AlertDmemUncorrectable = 1;
  parameter int AlertRegUncorrectable = 2;

  // Error codes
  typedef enum logic [31:0] {ErrCodeNoError = 32'h0000_0000} err_code_e;

  // Constants =====================================================================================

  typedef enum logic {
    InsnSubsetBase = 1'b0
    ,  // Base (RV32/Narrow) Instruction Subset
    InsnSubsetBignum = 1'b1  // Big Number (BN/Wide) Instruction Subset
  } insn_subset_e;

  // Opcodes (field [6:0] in the instruction), matching the RISC-V specification for the base
  // instruction subset.
  typedef enum logic [6:0] {
    InsnOpcodeBaseLoad = 7'h03,
    InsnOpcodeBaseMemMisc = 7'h0f,
    InsnOpcodeBaseOpImm = 7'h13,
    InsnOpcodeBaseAuipc = 7'h17,
    InsnOpcodeBaseStore = 7'h23,
    InsnOpcodeBaseOp = 7'h33,
    InsnOpcodeBaseLui = 7'h37,
    InsnOpcodeBaseBranch = 7'h63,
    InsnOpcodeBaseJalr = 7'h67,
    InsnOpcodeBaseJal = 7'h6f,
    InsnOpcodeBaseSystem = 7'h73
  } insn_opcode_e;

  typedef enum logic [3:0] {
    AluOpAdd,
    AluOpSub,

    AluOpXor,
    AluOpOr,
    AluOpAnd,
    AluOpNot,

    AluOpSra,
    AluOpSrl,
    AluOpSll
  } alu_op_e;

  typedef enum logic {
    ComparisonOpEq,
    ComparisonOpNeq
  } comparison_op_e;

  // Operand a source selection
  typedef enum logic [1:0] {
    OpASelRegister = 'd0,
    OpASelImmediate = 'd1,
    OpASelFwd = 'd2,
    OpASelCurrPc = 'd3
  } op_a_sel_e;

  // Operand b source selection
  typedef enum logic {
    OpBSelRegister = 1'b0,
    OpBSelImmediate = 1'b1
  } op_b_sel_e;


  // Immediate a selection
  typedef enum logic {ImmAZero} imm_a_sel_e;

  // Immediate b selection
  typedef enum logic [2:0] {
    ImmBI,
    ImmBS,
    ImmBB,
    ImmBU,
    ImmBJ
  } imm_b_sel_e;

  // Regfile write data selection
  typedef enum logic {RfWdSelEx} rf_wd_sel_e;

  // Control and Status Registers (CSRs)
  parameter int CsrNumWidth = 12;
  typedef enum logic [CsrNumWidth-1:0] {
    CsrFlags = 12'h7C0,
    CsrMod0 = 12'h7D0,
    CsrMod1 = 12'h7D1,
    CsrMod2 = 12'h7D2,
    CsrMod3 = 12'h7D3,
    CsrMod4 = 12'h7D4,
    CsrMod5 = 12'h7D5,
    CsrMod6 = 12'hdD6,
    CsrMod7 = 12'h7D7,
    CsrRnd = 12'hFC0
  } csr_e;

  // Wide Special Purpose Registers (WSRs)
  parameter int NWsr = 3;  // Number of WSRs
  parameter int WsrNumWidth = $clog2(NWsr);
  typedef enum logic [WsrNumWidth-1:0] {
    WsrMod = 'd0,
    WsrRnd = 'd1,
    WsrAcc = 'd2
  } wsr_e;
  // TODO: Figure out how to add assertions for the enum type width; initial blocks, as produced by
  // ASSERT_INIT, aren't allowed in packages.
  //`ASSERT_INIT(WsrESizeMatchesParameter_A, $bits(wsr_e) == WsrNumWidth)

  // Decoded instruction components, with signals matching the "Decoding" section of the
  // specification.
  // TODO: The variable names are rather short, especially "i" is confusing. Think about renaming.

  typedef struct packed {
    logic [4:0] d;  // Destination register
    logic [4:0] a;  // First source register
    logic [4:0] b;  // Second source register
    logic [31:0] i;  // Immediate
  } insn_dec_base_t;

  // Control signals from decoder to controller: additional information about the decoded
  // instruction influencing the operation.
  typedef struct packed {
    insn_subset_e subset;
    op_a_sel_e op_a_sel;
    op_b_sel_e op_b_sel;
    alu_op_e alu_op;
    logic rf_we;
    rf_wd_sel_e rf_wdata_sel;
    logic ecall_insn;
  } insn_dec_ctrl_t;

  typedef struct packed {
    alu_op_e op;
    logic [31:0] operand_a;
    logic [31:0] operand_b;
  } alu_base_operation_t;

  typedef struct packed {
    comparison_op_e op;
    logic [31:0] operand_a;
    logic [31:0] operand_b;
  } alu_base_comparison_t;

endpackage
