// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

package otbn_pkg;

  // Global Constants ==============================================================================

  // Data path width for BN (wide) instructions, in bits.
  parameter int WLEN = 256;

  // "Extended" WLEN: the size of the datapath with added integrity bits
  parameter int ExtWLEN = WLEN * 39 / 32;

  // Width of base (32b) data path with added integrity bits
  parameter int BaseIntgWidth = 39;

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

  parameter int SideloadKeyWidth = 384;


  // Toplevel constants ============================================================================

  parameter int AlertFatal = 0;
  parameter int AlertRecov = 1;

  // Register file implementation selection enum.
  typedef enum integer {
    RegFileFF    = 0, // Generic flip-flop based implementation
    RegFileFPGA  = 1  // FPGA implmentation, does infer RAM primitives.
  } regfile_e;

  // Command to execute. See the CMD register description in otbn.hjson for details.
  typedef enum logic [7:0] {
    CmdExecute     = 8'hd8,
    CmdSecWipeDmem = 8'hc3,
    CmdSecWipeImem = 8'h1e
  } cmd_e;

  // Status register values. See the STATUS register description in otbn.hjson for details.
  typedef enum logic [7:0] {
    StatusIdle            = 8'h00,
    StatusBusyExecute     = 8'h01,
    StatusBusySecWipeDmem = 8'h02,
    StatusBusySecWipeImem = 8'h03,
    StatusLocked          = 8'hFF
  } status_e;

  function automatic logic is_busy_status(status_e status);
    return status inside {StatusBusyExecute, StatusBusySecWipeDmem, StatusBusySecWipeImem};
  endfunction

  // Error bits
  //
  // Note: These errors are duplicated in other places. If updating them here, update those too.
  typedef struct packed {
    logic fatal_software;
    logic lifecycle_escalation;
    logic illegal_bus_access;
    logic bad_internal_state;
    logic bus_intg_violation;
    logic reg_intg_violation;
    logic dmem_intg_violation;
    logic imem_intg_violation;
    logic key_invalid;
    logic loop;
    logic illegal_insn;
    logic call_stack;
    logic bad_insn_addr;
    logic bad_data_addr;
  } err_bits_t;

  // All the error signals that can be generated directly from the controller. Note that this is
  // organised to include every software error (including 'call_stack', which actually gets fed in
  // from the base register file)
  typedef struct packed {
    logic fatal_software;
    logic bad_internal_state;
    logic reg_intg_violation;
    logic key_invalid;
    logic loop;
    logic illegal_insn;
    logic call_stack;
    logic bad_insn_addr;
    logic bad_data_addr;
  } controller_err_bits_t;

  // All the error signals that can be generated somewhere inside otbn_core
  typedef struct packed {
    logic fatal_software;
    logic bad_internal_state;
    logic reg_intg_violation;
    logic dmem_intg_violation;
    logic imem_intg_violation;
    logic key_invalid;
    logic loop;
    logic illegal_insn;
    logic call_stack;
    logic bad_insn_addr;
    logic bad_data_addr;
  } core_err_bits_t;

  // The error signals that are generated outside of otbn_core
  typedef struct packed {
    logic lifecycle_escalation;
    logic illegal_bus_access;
    logic bad_internal_state;
    logic bus_intg_violation;
  } non_core_err_bits_t;

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
    AluOpBignumNot
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
    RfWdSelMac,
    RfWdSelMovSel
  } rf_wd_sel_e;

  // Control and Status Registers (CSRs)
  parameter int CsrNumWidth = 12;
  typedef enum logic [CsrNumWidth-1:0] {
    // Address ranges follow the RISC-V Privileged Specification v1.11
    // 0x7C0-0x7FF Custom read/write
    CsrFg0         = 12'h7C0,
    CsrFg1         = 12'h7C1,
    CsrFlags       = 12'h7C8,
    CsrMod0        = 12'h7D0,
    CsrMod1        = 12'h7D1,
    CsrMod2        = 12'h7D2,
    CsrMod3        = 12'h7D3,
    CsrMod4        = 12'h7D4,
    CsrMod5        = 12'h7D5,
    CsrMod6        = 12'h7D6,
    CsrMod7        = 12'h7D7,
    CsrRndPrefetch = 12'h7D8,

    // 0xFC0-0xFFF Custom read-only
    CsrRnd         = 12'hFC0,
    CsrUrnd        = 12'hFC1
  } csr_e;

  // Wide Special Purpose Registers (WSRs)
  parameter int NWsr = 8; // Number of WSRs
  parameter int WsrNumWidth = $clog2(NWsr);
  typedef enum logic [WsrNumWidth-1:0] {
    WsrMod    = 'd0,
    WsrRnd    = 'd1,
    WsrUrnd   = 'd2,
    WsrAcc    = 'd3,
    WsrKeyS0L = 'd4,
    WsrKeyS0H = 'd5,
    WsrKeyS1L = 'd6,
    WsrKeyS1H = 'd7
  } wsr_e;

  // Internal Special Purpose Registers (ISPRs)
  // CSRs and WSRs have some overlap into what they map into. ISPRs are the actual registers in the
  // design which CSRs and WSRs are mapped on to.
  parameter int NIspr = 9;
  parameter int IsprNumWidth = $clog2(NIspr);
  typedef enum logic [IsprNumWidth-1:0] {
    IsprMod    = 'd0,
    IsprRnd    = 'd1,
    IsprAcc    = 'd2,
    IsprFlags  = 'd3,
    IsprUrnd   = 'd4,
    IsprKeyS0L = 'd5,
    IsprKeyS0H = 'd6,
    IsprKeyS1L = 'd7,
    IsprKeyS1H = 'd8
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

  // Structures for decoded instructions, grouped into three:
  // - insn_dec_shared_t - Anything that applies to both bignum and base microarchitecture
  // - insn_dec_base_t - Anything that only applies to the base side microarchitecture
  // - insn_dec_bignum_t - Anything that only applies to bignum side microarchitecture

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

    logic                    sel_insn;
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

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 4 -n 5 \
  //      -s 5799399942 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (66.67%)
  //  4: |||||||||| (33.33%)
  //  5: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 4

  localparam int StateControllerWidth = 5;
  typedef enum logic [StateControllerWidth-1:0] {
    OtbnStateHalt        = 5'b00100,
    OtbnStateRun         = 5'b01010,
    OtbnStateStall       = 5'b10011,
    OtbnStateLocked      = 5'b11101
  } otbn_state_e;

  // States for start_stop_controller
  // Encoding generated with:
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 8 -n 6 \
  //      -s 2798844836 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (57.14%)
  //  4: ||||||||||||||| (42.86%)
  //  5: --
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 5
  //
  localparam int StateStartStopWidth = 6;
  typedef enum logic [StateStartStopWidth-1:0] {
    OtbnStartStopStateHalt                = 6'b101000,
    OtbnStartStopStateUrndRefresh         = 6'b010000,
    OtbnStartStopStateRunning             = 6'b110011,
    OtbnStartStopSecureWipeWdrUrnd        = 6'b011101,
    OtbnStartStopSecureWipeAccModBaseUrnd = 6'b100101,
    OtbnStartStopSecureWipeAllZero        = 6'b111110,
    OtbnStartStopSecureWipeComplete       = 6'b001011,
    OtbnStartStopStateError               = 6'b000110
  } otbn_start_stop_state_e;

// Encoding generated with:
// $ ./util/design/sparse-fsm-encode.py -d 3 -m 4 -n 5 \
//      -s 2298830978 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: |||||||||||||||||||| (66.67%)
//  4: |||||||||| (33.33%)
//  5: --
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 4
// Minimum Hamming weight: 1
// Maximum Hamming weight: 4
//
localparam int StateScrambleCtrlWidth = 5;
typedef enum logic [StateScrambleCtrlWidth-1:0] {
  ScrambleCtrlIdle    = 5'b10011,
  ScrambleCtrlDmemReq = 5'b11110,
  ScrambleCtrlImemReq = 5'b01000,
  ScrambleCtrlError   = 5'b00101
} scramble_ctrl_state_e;

  // URNG PRNG default seed.
  // These parameters have been generated with
  // $ ./util/design/gen-lfsr-seed.py --width 256 --seed 2840984437 --prefix "Urnd"
  parameter int UrndPrngWidth = 256;
  typedef logic [UrndPrngWidth-1:0] urnd_prng_seed_t;
  parameter urnd_prng_seed_t RndCnstUrndPrngSeedDefault =
      256'h84ddfadaf7e1134d70aa1c59de6197ff25a4fe335d095f1e2cba89acbe4a07e9;

  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnKeyDefault =
      128'h14e8cecae3040d5e12286bb3cc113298;
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnNonceDefault =
      64'hf79780bc735f3843;

  typedef logic [63:0] otbn_dmem_nonce_t;
  typedef logic [63:0] otbn_imem_nonce_t;
endpackage
