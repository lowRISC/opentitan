// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

package otbn_pkg;

  // Global Constants ==============================================================================

  // Data path width for BN (wide) instructions, in bits. And its half and quarter size.
  parameter int WLEN  = 256;
  parameter int HWLEN = WLEN / 2;
  parameter int QWLEN = WLEN / 4;

  // "Extended" WLEN: the size of the datapath with added integrity bits
  parameter int ExtWLEN  = WLEN  * 39 / 32;
  parameter int ExtHWLEN = HWLEN * 39 / 32;
  parameter int ExtQWLEN = QWLEN * 39 / 32;

  // Width of base (32b) data path with added integrity bits
  parameter int BaseIntgWidth = 39;

  // Width of the base (32b) integrity part.
  parameter int BaseEccWidth = BaseIntgWidth - 32;

  // Number of 32-bit words per WLEN / HWLEN / QWLEN
  parameter int BaseWordsPerWLEN  = WLEN / 32;
  parameter int BaseWordsPerHWLEN = HWLEN / 32;
  parameter int BaseWordsPerQWLEN = QWLEN / 32;

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

  parameter int unsigned LoopStackDepth = 8;

  // Zero word in the implemented ECC scheme. If changing the ECC scheme, this has to be changed,
  // and vice-versa.
  localparam logic [BaseIntgWidth-1:0] EccZeroWord     = prim_secded_pkg::SecdedInv3932ZeroWord;
  localparam logic [ExtWLEN-1:0]       EccWideZeroWord = {BaseWordsPerWLEN{EccZeroWord}};

  // Size of DMEM scratch area. The total DMEM size is OTBN_DMEM_SIZE + DmemScratchSizeByte. Note
  // that some of the Python tooling depends on this parameter (it needs to know the full DMEM size,
  // but regtool only gives it OTBN_DMEM_SIZE). If changing this, you'll also need to edit
  // _DmemScratchSizeBytes in util/shared/mem_layout.py
  parameter int DmemScratchSizeByte = 16384;

  // Width of vector, in bits
  parameter int VLEN = WLEN;

  // Width of the smallest vector chunk we operate on, in bits
  parameter int VChunkLEN = 32;

  // Number of vector chunk processing elements
  parameter int NVecProc = VLEN / VChunkLEN;

  // A type to split a base word into integrity and data bits.
  typedef struct packed {
    logic [BaseEccWidth-1:0] intg;
    logic [31:0]             word;
  } otbn_base_intg_word_t;

  // A wide register (WDR or WSR) split into base words with integrity and data each.
  typedef otbn_base_intg_word_t [BaseWordsPerWLEN-1:0] otbn_wide_intg_word_t;

  // The URND partial seed width depends on the EDN interface.
  parameter int unsigned UrndPartialSeedWidth = edn_pkg::ENDPOINT_BUS_WIDTH;

  // Toplevel constants ============================================================================

  parameter int AlertFatal = 0;
  parameter int AlertRecov = 1;

  // Register file implementation selection enum.
  typedef enum integer {
    RegFileFF    = 0, // Generic flip-flop based implementation
    RegFileFPGA  = 1  // FPGA implementation, does infer RAM primitives.
  } regfile_e;

  // Command to execute. See the CMD register description in otbn.hjson for details.
  typedef enum logic [7:0] {
    CmdExecute     = 8'hd8,
    CmdSecWipeDmem = 8'hc3,
    CmdSecWipeImem = 8'h1e,
    CmdResume      = 8'ha6
  } cmd_e;

  // Status register values. See the STATUS register description in otbn.hjson for details.
  typedef enum logic [7:0] {
    StatusIdle            = 8'h00,
    StatusBusyExecute     = 8'h01,
    StatusBusySecWipeDmem = 8'h02,
    StatusBusySecWipeImem = 8'h03,
    StatusBusySecWipeInt  = 8'h04,
    StatusPaused          = 8'h05,
    StatusLocked          = 8'hFF
  } status_e;

  function automatic logic is_busy_status(status_e status);
    return status inside {StatusBusyExecute,
                          StatusBusySecWipeDmem,
                          StatusBusySecWipeImem,
                          StatusBusySecWipeInt};
  endfunction

  // Error bits
  //
  // Note: These errors are duplicated in other places. If updating them here, update those too.
  typedef struct packed {
    logic mai_error;
    logic fatal_software;
    logic lifecycle_escalation;
    logic illegal_bus_access;
    logic bad_internal_state;
    logic bus_intg_violation;
    logic reg_intg_violation;
    logic dmem_intg_violation;
    logic imem_intg_violation;
    logic rnd_fips_chk_fail;
    logic rnd_rep_chk_fail;
    logic key_invalid;
    logic loop;
    logic illegal_insn;
    logic call_stack;
    logic bad_insn_addr;
    logic bad_data_addr;
  } err_bits_t;

  // Wrappers for classifying bad internal states
  typedef struct packed {
    logic alu_bignum_err;
    logic mac_bignum_err;
    logic ispr_bignum_err;
    logic controller_err;
    logic rf_err;
    logic rd_err;
  } predec_err_t;

  typedef struct packed {
    logic spr_urnd_acks;
    logic spr_rnd_acks;
    logic spr_secwipe_reqs;
    logic mubi_rma_err;
    logic mubi_urnd_err;
    logic state_err;
  } start_stop_bad_int_t;

  typedef struct packed {
    logic loop_hw_cnt_err;
    logic loop_hw_stack_cnt_err;
    logic loop_hw_intg_err;
    logic rf_base_call_stack_err;
    logic spr_secwipe_acks;
    logic state_err;
    logic controller_mubi_err;
  } controller_bad_int_t;

  typedef struct packed {
    logic imem_gnt_missed_err;
    logic dmem_gnt_missed_err;
  } missed_gnt_t;

  typedef struct packed {
    logic rf_base_intg_err;
    logic rf_bignum_intg_err;
    logic mod_ispr_intg_err;
    // mac_ispr_intg_err includes the ACC WSR and the hidden registers for Montgomery computation
    logic mac_ispr_intg_err;
    logic loop_stack_addr_intg_err;
    logic insn_fetch_intg_err;
  } internal_intg_err_t;

  // All the error signals that can be generated directly from the controller. Note that this is
  // organised to include every software error (including 'call_stack', which actually gets fed in
  // from the base register file)
  typedef struct packed {
    logic mai_error;
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
    logic mai_error;
    logic fatal_software;
    logic bad_internal_state;
    logic reg_intg_violation;
    logic dmem_intg_violation;
    logic imem_intg_violation;
    logic rnd_fips_chk_fail;
    logic rnd_rep_chk_fail;
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
    InsnOpcodeBignumVec      = 7'h5B,
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

  typedef enum logic [4:0] {
    AluOpBignumAdd,
    AluOpBignumAddc,
    AluOpBignumAddm,
    AluOpBignumAddv,
    AluOpBignumAddvm,

    AluOpBignumSub,
    AluOpBignumSubb,
    AluOpBignumSubm,
    AluOpBignumSubv,
    AluOpBignumSubvm,

    AluOpBignumRshi,
    AluOpBignumShv,

    AluOpBignumXor,
    AluOpBignumOr,
    AluOpBignumAnd,
    AluOpBignumNot,

    AluOpBignumTrn1,
    AluOpBignumTrn2,

    AluOpBignumPack,
    AluOpBignumUnpk,

    AluOpBignumNone
  } alu_op_bignum_e;

  typedef enum logic [1:0] {
    AluOpLogicXor = 2'h0,
    AluOpLogicOr  = 2'h1,
    AluOpLogicAnd = 2'h2,
    AluOpLogicNot = 2'h3
  } alu_op_logic_e;

  typedef enum logic {
    AluShiftOpFull  = 1'b0,
    AluShiftOpDense = 1'b1
  } alu_shifter_op_e;

  typedef enum logic {
    AluShiftDirLeft  = 1'b0,
    AluShiftDirRight = 1'b1
  } alu_shifter_dir_e;

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

  // Number of ALU element lengths (ELEN)
  parameter int NELEN_ALU = 2;

  // Vector element length type for bignum vec ISA implemented in BN ALU for
  // bn.addv(m), bn.subv(m) and bn.shv.
  // The ISA foresees 4 types (16 to 128 bits) but only a subset is implemented.
  // In addition, vectorized instructions use the same hardware as regular instructions and thus
  // we need also a 256b type.
  typedef enum logic {
    AluElen32  = 1'h0,
    AluElen256 = 1'h1
  } alu_elen_e;

  // Number of transpose element lengths (ELEN)
  parameter int NELEN_TRN = 3;

  // Vector element length type for bignum instructions bn.trn1 and bn.trn2.
  // The ISA foresees 4 types (16 to 128 bits) but only a subset is implemented.
  typedef enum logic [1:0] {
    TrnElen32  = 2'b00,
    TrnElen64  = 2'b01,
    TrnElen128 = 2'b10
  } trn_elen_e;

  // Number of BN MAC ELENs
  parameter int NELEN_MAC = 2;

  // Vector element length type for bignum vec ISA implemented in BN MAC
  // The instructions supported by BN MAC support 2 types: vectorized 32-bit elements and the
  // regular 64-bit multiplication.
  typedef enum logic {
    MacElen32 = 1'b0,
    MacElen64 = 1'b1
  } mac_elen_e;

  // A BN MAC internal signal exposed for predecoding reasons. Selects the input for multiplier
  // operand B.
  typedef enum logic [1:0] {
    MulOpB,
    MulOpMu,
    MulOpq
  } mac_mul_op_b_sel_e;

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
    CsrUrndCtrl    = 12'h7D9,
    CsrKmacStatus  = 12'h7db,
    CsrKmacCtrl    = 12'h7dc,
    CsrKmacCfg     = 12'h7dd,
    CsrKmacStrb    = 12'h7de,
    CsrMaiCtrl     = 12'h7e0,

    // 0xFC0-0xFFF Custom read-only
    CsrRnd         = 12'hFC0,
    CsrUrnd        = 12'hFC1,
    CsrUrndStatus  = 12'hFC2,
    CsrInsnCnt     = 12'hFC3,
    CsrMaiStatus   = 12'hFCA
  } csr_e;

  // Wide Special Purpose Registers (WSRs)
  parameter int NWsr = 17; // Number of WSRs
  parameter int WsrNumWidth = $clog2(NWsr);
  typedef enum logic [WsrNumWidth-1:0] {
    WsrMod        = 'd0,
    WsrRnd        = 'd1,
    WsrUrnd       = 'd2,
    WsrAcc        = 'd3,
    WsrKeyS0L     = 'd4,
    WsrKeyS0H     = 'd5,
    WsrKeyS1L     = 'd6,
    WsrKeyS1H     = 'd7,
    WsrKmacDataS0 = 'd8,
    WsrKmacDataS1 = 'd9,
    WsrMaiResS0   = 'd10,
    WsrMaiResS1   = 'd11,
    WsrMaiIn0S0   = 'd12,
    WsrMaiIn0S1   = 'd13,
    WsrMaiIn1S0   = 'd14,
    WsrMaiIn1S1   = 'd15,
    WsrUrndState  = 'd16
  } wsr_e;

  // Internal Special Purpose Registers (ISPRs)
  // CSRs and WSRs have some overlap into what they map into. ISPRs are the actual registers in the
  // design which CSRs and WSRs are mapped on to.
  parameter int NIspr = 27;
  parameter int IsprNumWidth = $clog2(NIspr);
  typedef enum logic [IsprNumWidth-1:0] {
    IsprMod        = 'd0,
    IsprRnd        = 'd1,
    IsprAcc        = 'd2,
    IsprFlags      = 'd3,
    IsprUrnd       = 'd4,
    IsprKeyS0L     = 'd5,
    IsprKeyS0H     = 'd6,
    IsprKeyS1L     = 'd7,
    IsprKeyS1H     = 'd8,
    IsprMaiResS0   = 'd9,
    IsprMaiResS1   = 'd10,
    IsprMaiIn0S0   = 'd11,
    IsprMaiIn0S1   = 'd12,
    IsprMaiIn1S0   = 'd13,
    IsprMaiIn1S1   = 'd14,
    IsprMaiCtrl    = 'd15,
    IsprMaiStatus  = 'd16,
    IsprKmacDataS0 = 'd17,
    IsprKmacDataS1 = 'd18,
    IsprKmacStatus = 'd19,
    IsprKmacCtrl   = 'd20,
    IsprKmacCfg    = 'd21,
    IsprKmacStrb   = 'd22,
    IsprInsnCnt    = 'd23,
    IsprUrndState  = 'd24,
    IsprUrndCtrl   = 'd25,
    IsprUrndStatus = 'd26
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
    insn_subset_e           subset;
    logic                   ecall_insn;
    logic                   wfi_insn;
    logic                   ld_insn;
    logic                   st_insn;
    logic                   branch_insn;
    logic                   jump_insn;
    logic                   loop_insn;
    logic                   ispr_rd_insn;
    logic                   ispr_wr_insn;
    logic                   ispr_rs_insn;
    logic [NFlagGroups-1:0] ispr_flags_wr;
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

    alu_elen_e               alu_elen;
    trn_elen_e               trn_elen;
    logic                    alu_adder_carry_sel;
    // Shifting only applies to a subset of ALU operations
    logic [$clog2(WLEN)-1:0] alu_shift_amt;   // Shift amount
    logic                    alu_shift_right; // Shift right if set otherwise left
    // Shift mask for vectorized shifting. Replicated for all chunks.
    logic [VChunkLEN-1:0]    alu_shift_mask;

    flag_group_t             alu_flag_group;
    flag_e                   alu_sel_flag;
    logic                    alu_flag_en;
    alu_op_bignum_e          alu_op;
    op_b_sel_e               alu_op_b_sel;

    logic                    mac_flag_en;
    logic [1:0]              mac_op_a_qw_sel_raw;
    logic [2:0]              mac_op_b_elem0_sel_raw;
    logic [2:0]              mac_op_b_elem1_sel_raw;
    logic                    mac_wr_hw_sel_upper;
    logic [1:0]              mac_pre_acc_shift;
    logic                    mac_acc_add_en;
    logic                    mac_shift_out;
    logic                    mac_en;
    logic                    mac_is_vec;
    logic                    mac_is_mod;
    logic                    mac_is_lane;
    mac_elen_e               mac_elen;
    logic [VLEN/QWLEN-1:0]   mac_adder_carry_sel;
    logic [2:0]              mac_lane_index;

    logic                    rf_we;
    rf_wd_sel_e              rf_wdata_sel;
    logic                    rf_ren_a;
    logic                    rf_ren_b;

    logic                    sel_insn;
  } insn_dec_bignum_t;

  typedef struct packed {
    logic [NWdr-1:0] rf_ren_a;
    logic [NWdr-1:0] rf_ren_b;
    logic [NWdr-1:0] rf_we;
  } rf_bignum_predec_t;

  typedef struct packed {
    // ALU
    alu_elen_e               alu_elen;
    logic                    adder_x_en;
    logic                    x_res_operand_a_sel;
    logic                    adder_y_op_a_en;
    logic                    shift_mod_sel;
    logic                    unpack_shifter_en;
    logic                    adder_y_op_shifter_en;
    logic [NVecProc-1:0]     adder_x_carries_in;
    logic                    adder_x_op_b_invert;
    logic [NVecProc-2:0]     adder_y_carries_top; // The adder Y carries except the LSB carry
    logic                    adder_y_op_b_invert;
    logic                    adder_carry_sel;
    logic                    mod_is_subtraction;
    // Shifter
    logic [1:0]              shift_op_a_sel;
    logic [1:0]              shift_op_b_sel;
    logic [1:0]              shift_dir;
    logic [$clog2(WLEN)-1:0] shift_amt;
    logic [VChunkLEN-1:0]    shift_mask;
    // Logic
    logic                    logic_a_en;
    logic                    logic_shifter_en;
    logic [3:0]              logic_res_sel;
    // Vector transposer
    trn_elen_e               trn_elen;
    logic                    trn_en;
    logic                    trn_is_trn1;
    // Flags
    logic [NFlagGroups-1:0]  flag_group_sel;
    flags_t                  flag_sel;
    logic [NFlagGroups-1:0]  flags_keep;
    logic [NFlagGroups-1:0]  flags_adder_update;
    logic [NFlagGroups-1:0]  flags_logic_update;
    logic [NFlagGroups-1:0]  flags_mac_update;
    logic [NFlagGroups-1:0]  flags_ispr_wr;
  } alu_bignum_predec_t;

  typedef struct packed {
    logic [NIspr-1:0] ispr_rd_en;
    logic [NIspr-1:0] ispr_wr_en;
  } ispr_bignum_predec_t;

  typedef struct packed {
    logic                  mac_en;
    logic                  is_vec;
    logic                  is_mod;
    logic                  is_lane;
    logic [2:0]            lane_index;
    mac_elen_e             elen;
    logic [1:0]            shuffle_offset;
    logic [VLEN/QWLEN-1:0] adder_carry_sel;
    logic                  acc_add_en;
    logic [1:0]            op_a_qw_sel;      // Both (a, b) are predecoded to optimize timing
    logic [2:0]            op_b_elem0_sel;   // Operand B is mux on lane level
    logic [2:0]            op_b_elem1_sel;
    logic                  mul_op_a_tmp_sel; // Predecoded to optimize timing
    mac_mul_op_b_sel_e     mul_op_b_sel;     // Predecoded to optimize timing
    logic                  mul_add_en;
    logic                  c_add_en;
    logic                  add_mod_en;
    logic [VLEN/QWLEN-1:0] acc_qw_sel;
    logic                  acc_merger_en;
    logic                  mul_shift_en;
    logic                  mul_merger_en;
    logic                  add_res_en;
    logic                  operation_valid_raw;
  } mac_bignum_predec_t;

  typedef struct packed {
    logic tmp_wr_en_raw;
    logic tmp_clear_en;
    logic c_wr_en_raw;
    logic c_clear_en;
    logic acc_wr_en_raw;
    logic acc_clear_en;
  } mac_bignum_contrl_t;

  typedef struct packed {
    logic call_stack_pop;
    logic call_stack_push;
    logic branch_insn;
    logic jump_insn;
    logic loop_insn;
    logic sel_insn;
  } ctrl_flow_predec_t;

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
    alu_elen_e               alu_elen;
    trn_elen_e               trn_elen;
    logic                    adder_carry_sel;
    logic                    shift_right;
    logic [$clog2(WLEN)-1:0] shift_amt;
    logic [VChunkLEN-1:0]    shift_mask;
    flag_group_t             flag_group;
    flag_e                   sel_flag;
    logic                    alu_flag_en;
    logic                    mac_flag_en;
  } alu_bignum_operation_t;

  typedef struct packed {
    logic [WLEN-1:0]       operand_a;
    logic [WLEN-1:0]       operand_b;
    // The raw select signals are used as input to the FSM which then computes the actual selection
    // signals. Effectively used are the predecoded ones.
    logic [1:0]            op_a_qw_sel_raw;
    logic [2:0]            op_b_elem0_sel_raw;
    logic [2:0]            op_b_elem1_sel_raw;
    logic                  wr_hw_sel_upper;
    logic [1:0]            pre_acc_shift_imm;
    logic                  acc_add_en;
    logic                  shift_acc;
    logic                  is_vec;
    logic                  is_mod;
    logic                  is_lane;
    mac_elen_e             elen;
    logic [VLEN/QWLEN-1:0] adder_carry_sel;
    logic [2:0]            lane_index;
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
  // Encoding generated at commit 8e0414b5fc using Python 3.10.19 with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv \
  //     --seed 573771984 --distance 3 --states 10 --bits 8
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (31.11%)
  //  4: |||||||||||||||||||| (31.11%)
  //  5: |||||||||||| (20.00%)
  //  6: |||||||| (13.33%)
  //  7: || (4.44%)
  //  8: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 7
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 6
  //
  localparam int StateStartStopWidth = 8;
  typedef enum logic [StateStartStopWidth-1:0] {
    OtbnStartStopStateInitial             = 8'b10100111,
    OtbnStartStopStateHalt                = 8'b00000001,
    OtbnStartStopStateUrndRefresh         = 8'b11110010,
    OtbnStartStopStateRunning             = 8'b01110111,
    OtbnStartStopSecureWipeWdrUrnd        = 8'b10010000,
    OtbnStartStopSecureWipeAccModBaseUrnd = 8'b10001110,
    OtbnStartStopSecureWipeExtIsprsUrnd   = 8'b00110100,
    OtbnStartStopSecureWipeAllZero        = 8'b01111000,
    OtbnStartStopSecureWipeComplete       = 8'b10101001,
    OtbnStartStopStateLocked              = 8'b01101101
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
  typedef prim_trivium_pkg::trivium_lfsr_seed_t urnd_prng_seed_t;
  parameter urnd_prng_seed_t RndCnstUrndPrngSeedDefault =
      urnd_prng_seed_t'(prim_trivium_pkg::RndCnstTriviumLfsrSeedDefault);

  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnKeyDefault =
      128'h14e8cecae3040d5e12286bb3cc113298;
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnNonceDefault =
      64'hf79780bc735f3843;

  typedef logic [63:0] otbn_dmem_nonce_t;
  typedef logic [63:0] otbn_imem_nonce_t;

  // Permutation for the URND permutation in BN MAC used for register clearing and shuffling.
  // Keep in sync with dv/otbnsim/sim/constants.py::BN_MAC_PERMUTATION.
  // These parameters have been generated at commit 72ff50ed19 using Python 3.10.13 with
  // $ ./util/design/gen-lfsr-seed.py --width 256 --seed 3357506447 --prefix "BnMac"
  // and replaced "Lfsr" with "UrndPerm" and "lfsr_" with "urnd_".
  parameter int BnMacUrndPermWidth = 256;
  typedef logic [BnMacUrndPermWidth-1:0][$clog2(BnMacUrndPermWidth)-1:0] bn_mac_urnd_perm_t;
  parameter bn_mac_urnd_perm_t RndCnstBnMacUrndPermDefault = {
    256'h5883853c_f22faef4_c975ab18_050bfc6b_b9193e1b_450d686e_5de1cdb5_a02a1532,
    256'ha3e9dd76_8278f6d4_33f74bd9_edbabd7f_721c5a4e_0c23a6f0_34a477db_84947998,
    256'h6d0affec_df12e025_0fb41ab3_3bdc90e5_ce279907_91227bf1_e4505bcc_2b4c31be,
    256'h562047c5_9df5fd21_73acadc3_b1438b53_bc8e87a1_d7b02e88_16de0e97_6c354669,
    256'he89657fe_2662402d_03e3a849_1f6ff839_668c5574_54e2bf14_9cbb8dd3_d5d1ea81,
    256'h92c73f60_6402b793_52b68911_5161cb7a_09aacab2_0604865f_4dd8d201_101e08c1,
    256'h7c95a23a_ef177de6_d65c418f_daa96a70_5929c83d_fafb9f37_8a4436af_a5a71d13,
    256'hcf48c07e_42d0eb67_c29b3863_9a28e72c_b880f3ee_9e246571_00c6f9c4_4f305e4a
  };

  // Permutation for the URND randomness feeding the mask accelerator gadgets in MAI.
  // Keep in sync with dv/otbnsim/sim/constants.py::MAI_URND_PERMUTATION.
  // These parameters have been generated at commit 72ff50ed19 using Python 3.10.13 with
  // $ ./util/design/gen-lfsr-seed.py --width 389 --seed 1478636329 --prefix "Mai"
  // and replaced "Lfsr" with "UrndPerm" and "lfsr_" with "urnd_".
  parameter int MaiUrndPermWidth = 389;
  typedef logic [MaiUrndPermWidth-1:0][$clog2(MaiUrndPermWidth)-1:0] mai_urnd_perm_t;
  parameter mai_urnd_perm_t RndCnstMaiUrndPermDefault = {
    173'h113b_75b40630_bb30dd72_f54be9c3_4625b01b_40a768d1,
    256'haa422858_e28c712b_7aac1117_5dc94024_1d657838_819f2969_1399c966_8e49cc53,
    256'ha35adab0_64898614_88a67384_b8f743c1_b9d44b26_50f0c51f_34a5e7ee_f690bce9,
    256'h5d133e2b_f642a5ac_a7209d30_5517a5ea_b83ccf61_0cc6c609_f41c3b33_4b23d00d,
    256'h707c86fc_6e6649e0_b823c55d_fcab7b87_048db103_f21b3672_b62608a9_63a2ff22,
    256'h264a9774_52d444d6_4d6ca94b_29410e06_771c18a4_16c1b5fa_55a60e32_17a129fa,
    256'h4d35047e_a0588565_f505f1ed_52859d69_e7792a2e_98a7bc27_8ff39225_0a14cb9a,
    256'h0a1c0e64_0819ac16_37b46df8_08ad9a57_0eba3261_e1006a1e_cf5a2ebd_248081fb,
    256'hc5425b21_bc94d16b_61a11935_1c9259c8_6a24029c_048d2728_e00154e2_2e8d799a,
    256'h85829555_ee105c1e_ad608846_29449c40_0900532f_90d4f4ec_af0ac1ad_5325d11c,
    256'hacd07ea4_89ef58ca_6a4c1363_260af536_f9b6ab79_11ac2507_d24596b8_3e892f80,
    256'ha7a0ccdd_b8ec4dc0_6eb1b6e8_52e6f07f_d2ac20c5_c9b2315e_8f222a03_b0f81e20,
    256'ha4b9580e_2418e8b5_c74813e1_14768750_267885b4_9542f237_72b4f2e4_30ca4cd2,
    256'hd2c0e844_c805dc2e_30223335_d3546a50_56eb8beb_edc4c45a_0dcc618a_8d60cab1
  };

  // Permutation applied to the primary URND output in otbn_rnd, directly after the Bivium PRNG
  // and before it is flopped and fanned out to every URND consumer in the design.
  // Keep in sync with dv/otbnsim/sim/constants.py::URND_PERMUTATION.
  // These parameters have been generated at commit 72ff50ed19 using Python 3.10.13 with
  // $ ./util/design/gen-lfsr-seed.py --width 389 --seed 3141592653 --prefix ""
  // and replaced "Lfsr" with "UrndPerm" and "lfsr_" with "urnd_".
  parameter int UrndPermWidth = 389;
  typedef logic [UrndPermWidth-1:0][$clog2(UrndPermWidth)-1:0] urnd_perm_t;
  parameter urnd_perm_t RndCnstUrndPermDefault = {
    173'h0978_8cf1d647_48c85a94_0884c1aa_e1b4c286_869b82e2,
    256'hed624787_98726008_460f5dbe_5947d383_33426939_a9968ac9_453142a3_73a555e9,
    256'h2f962b66_2c5885ca_4c8f4b1d_540d58bd_a488a337_318212a1_1b051812_bbc465fd,
    256'h18642ae9_ebe38989_d0ba9d45_f0125834_3506ff9f_2aafc5eb_cda2b854_062169b5,
    256'h932cd5c0_37914c53_2ccc221e_6ce49046_d36ac0f8_4ac10c94_1d0d92c1_d972a0db,
    256'h870e5c6b_6808387f_00029e5b_d2e3fc08_da423b13_b02b3adb_35d27b14_2bca73f1,
    256'h20e2fad6_71568004_69ddb5a4_15b5d114_e4cc1a34_06b97949_ece1b96b_9446103c,
    256'h104e6eea_a254df6a_3e202980_769985a2_9f52474a_a52191a8_3a3d4312_a556c35b,
    256'h628e2a39_0b84d644_988976b0_a7204f44_9b78bdd8_6e8a3e95_2fba18b1_be04a92f,
    256'h60add12e_0a831589_3f41e9da_416e3f2f_0ba586b4_676d7918_b5ab071a_e894c50a,
    256'h6edc2180_9408299a_79781605_b69ec51b_fdd4744b_4217e642_10c516cc_1a7ba683,
    256'h2c61e48d_10f36246_8ee2d181_36087564_a2c13245_733cae48_7a98d62a_d18aa0d0,
    256'h4faf9c19_6ea3f242_e40d2cdb_ae313051_75684460_de994131_3a714af8_6722a7a6,
    256'h71047a06_b215bc6e_eefb0b0a_e8a2782f_e111c7e0_a5ce0820_31cfaa34_72de1f4b
  };

  // Encoding generated at commit 2f740b6f5b using Python 3.10.19 with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv \
  //     --seed 2298832222 --distance 3 --states 4 --bits 5
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
  localparam int MaskOpWidth = 5;
  typedef enum logic [MaskOpWidth-1:0] {
    SecAdd      = 5'b10111,
    SecAddMod   = 5'b01100,
    ArithToBool = 5'b01011,
    BoolToArith = 5'b10000
  } mask_op_e;

  // Number of shares used inside the mask accelerator
  parameter int unsigned NumShares = 2;

  // Bit width of the secure adder pipeline (otbn_sec_add / otbn_sec_add_mod)
  parameter int unsigned SecAddWidth = 32;

  // Convenience types for mask-accelerator element and share-pair values.
  typedef logic [SecAddWidth-1:0]  ma_ele_t;
  typedef ma_ele_t [NumShares-1:0] ma_sharing_t;

  // Batch size of the modular secure adder pipeline (otbn_sec_add_mod)
  parameter int unsigned SecAddVecSize = 8;

  // Randomness input width for an otbn_sec_add instance of a given bit width.
  // Derived from the HPC3 gadget count across the pre-compute stage and the log2(width)
  // prefix-tree stages. Only valid for power-of-two widths.
  function automatic int unsigned SecAddRandWidth(int unsigned width);
    return 32'd2 * ($clog2(width) * width + 32'd1);
  endfunction

  // Width of randomness required by the mask accelerator
  localparam int unsigned MaRndLen = SecAddRandWidth(SecAddWidth);

  // Output width of OTBN's Bivium URND.
  //
  // The MAI pipeline (mai_ma_urnd_t in otbn_mai.sv) sets the minimum required width. The 322-bit
  // otbn_sec_add randomness is consumed fresh every cycle while otbn_sec_add is running. The two
  // remasking words are consumed fresh every input cycle of a batch. The batch-counter start value
  // is consumed once per batch.
  localparam int unsigned UrndLen =
      SecAddRandWidth(SecAddWidth)  // 322: consumed every cycle while otbn_sec_add runs
      + 2 * int'(SecAddWidth)       //  64: two remasking words, consumed every input cycle
      + $clog2(BaseWordsPerWLEN);   //   3: randomised batch-counter start value

  // A type to select bits from URND to secure wipe a full WSR.
  localparam int unsigned IsprRndRsvdWidth = UrndLen - ExtWLEN;

  typedef struct packed {
    logic [IsprRndRsvdWidth-1:0] rsvd;
    logic [ExtWLEN-1:0]          urnd;
  } otbn_ispr_urnd_t;

endpackage
