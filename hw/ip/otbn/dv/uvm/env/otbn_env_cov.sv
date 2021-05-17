// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class otbn_env_cov extends cip_base_env_cov #(.CFG_T(otbn_env_cfg));
  `uvm_component_utils(otbn_env_cov)

  // A field for each known mnemonic, cast to a mnem_str_t. We have to do this because VCS (at
  // least) complains if you put an uncast string literal in a position where it expects an integral
  // value.
`define DEF_MNEM(MNEM_NAME, MNEMONIC) \
  mnem_str_t MNEM_NAME = mnem_str_t'(MNEMONIC)
  `DEF_MNEM(mnem_add,           "add");
  `DEF_MNEM(mnem_addi,          "addi");
  `DEF_MNEM(mnem_lui,           "lui");
  `DEF_MNEM(mnem_sub,           "sub");
  `DEF_MNEM(mnem_sll,           "sll");
  `DEF_MNEM(mnem_slli,          "slli");
  `DEF_MNEM(mnem_srl,           "srl");
  `DEF_MNEM(mnem_srli,          "srli");
  `DEF_MNEM(mnem_sra,           "sra");
  `DEF_MNEM(mnem_srai,          "srai");
  `DEF_MNEM(mnem_and,           "and");
  `DEF_MNEM(mnem_andi,          "andi");
  `DEF_MNEM(mnem_or,            "or");
  `DEF_MNEM(mnem_ori,           "ori");
  `DEF_MNEM(mnem_xor,           "xor");
  `DEF_MNEM(mnem_xori,          "xori");
  `DEF_MNEM(mnem_lw,            "lw");
  `DEF_MNEM(mnem_sw,            "sw");
  `DEF_MNEM(mnem_beq,           "beq");
  `DEF_MNEM(mnem_bne,           "bne");
  `DEF_MNEM(mnem_jal,           "jal");
  `DEF_MNEM(mnem_jalr,          "jalr");
  `DEF_MNEM(mnem_csrrs,         "csrrs");
  `DEF_MNEM(mnem_csrrw,         "csrrw");
  `DEF_MNEM(mnem_ecall,         "ecall");
  `DEF_MNEM(mnem_loop,          "loop");
  `DEF_MNEM(mnem_loopi,         "loopi");
  `DEF_MNEM(mnem_bn_add,        "bn.add");
  `DEF_MNEM(mnem_bn_addc,       "bn.addc");
  `DEF_MNEM(mnem_bn_addi,       "bn.addi");
  `DEF_MNEM(mnem_bn_addm,       "bn.addm");
  `DEF_MNEM(mnem_bn_mulqacc,    "bn.mulqacc");
  `DEF_MNEM(mnem_bn_mulqacc_wo, "bn.mulqacc.wo");
  `DEF_MNEM(mnem_bn_mulqacc_so, "bn.mulqacc.so");
  `DEF_MNEM(mnem_bn_sub,        "bn.sub");
  `DEF_MNEM(mnem_bn_subb,       "bn.subb");
  `DEF_MNEM(mnem_bn_subi,       "bn.subi");
  `DEF_MNEM(mnem_bn_subm,       "bn.subm");
  `DEF_MNEM(mnem_bn_and,        "bn.and");
  `DEF_MNEM(mnem_bn_or,         "bn.or");
  `DEF_MNEM(mnem_bn_not,        "bn.not");
  `DEF_MNEM(mnem_bn_xor,        "bn.xor");
  `DEF_MNEM(mnem_bn_rshi,       "bn.rshi");
  `DEF_MNEM(mnem_bn_sel,        "bn.sel");
  `DEF_MNEM(mnem_bn_cmp,        "bn.cmp");
  `DEF_MNEM(mnem_bn_cmpb,       "bn.cmpb");
  `DEF_MNEM(mnem_bn_lid,        "bn.lid");
  `DEF_MNEM(mnem_bn_sid,        "bn.sid");
  `DEF_MNEM(mnem_bn_mov,        "bn.mov");
  `DEF_MNEM(mnem_bn_movr,       "bn.movr");
  `DEF_MNEM(mnem_bn_wsrr,       "bn.wsrr");
  `DEF_MNEM(mnem_bn_wsrw,       "bn.wsrw");
`undef DEF_MNEM

  // A macro used for coverpoints for mnemonics. This expands to entries like
  //
  //    bins mnem_add = {mnem_add};
`define DEF_MNEM_BIN(NAME) bins NAME = {NAME}

  // Cross one, two or three coverpoints with mnemonic_cp.
  //
  // This is intentended to be used inside covergroups that support multiple instructions. In each
  // of these, we define a coverpoint called mnemonic_cp to track which instruction is being
  // sampled.
`define DEF_MNEM_CROSS(BASENAME)                                         \
    BASENAME``_cross: cross BASENAME``_cp, mnemonic_cp;
`define DEF_MNEM_CROSS2(BASE0, BASE1)                                    \
    BASE0``_``BASE1``_cross: cross BASE0``_cp, BASE1``_cp, mnemonic_cp;
`define DEF_MNEM_CROSS3(BASE0, BASE1, BASE2)                             \
    BASE0``_``BASE1``_``BASE2``_cross:                                   \
      cross BASE0``_cp, BASE1``_cp, BASE2``_cp, mnemonic_cp;

  // A macro to define bins for GPR types. The point is that there are 3 interesting types of GPR:
  // x0, x1 and everything else.
`define GPR_BIN_TYPES \
  { bins gpr_x0 = {5'd0}; bins gpr_x1 = {5'd1}; bins gpr_other = {[5'd2:$]}; }

  // Declare a GPR coverpoint with the 3 types above
`define DEF_GPR_CP(NAME, BITS) \
  NAME: coverpoint insn_data[BITS] `GPR_BIN_TYPES

  // Per-encoding covergroups
  covergroup enc_bna_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    // Used for bna and bnaf encodings (which have the same operand layout: the only difference is
    // in the layout of the fixed bits)
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_add);
      `DEF_MNEM_BIN(mnem_bn_addc);
      `DEF_MNEM_BIN(mnem_bn_sub);
      `DEF_MNEM_BIN(mnem_bn_subb);
      `DEF_MNEM_BIN(mnem_bn_and);
      `DEF_MNEM_BIN(mnem_bn_or);
      `DEF_MNEM_BIN(mnem_bn_xor);
      illegal_bins other = default;
    }

    sb_cp: coverpoint insn_data[29:25] { bins extremes[] = {'0, '1}; }
    st_cp: coverpoint insn_data[30];
    fg_cp: coverpoint insn_data[31];

    `DEF_MNEM_CROSS(sb)
    `DEF_MNEM_CROSS(st)
    `DEF_MNEM_CROSS(fg)
  endgroup

  covergroup enc_bnai_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_addi);
      `DEF_MNEM_BIN(mnem_bn_subi);
      illegal_bins other = default;
    }

    imm_cp: coverpoint insn_data[29:20] { bins extremes[] = {'0, '1}; }
    fg_cp: coverpoint insn_data[31];

    `DEF_MNEM_CROSS(imm)
    `DEF_MNEM_CROSS(fg)
  endgroup

  covergroup enc_bnam_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_addm);
      `DEF_MNEM_BIN(mnem_bn_subm);
      illegal_bins other = default;
    }

  endgroup

  covergroup enc_bnan_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_not);
      illegal_bins other = default;
    }

    sb_cp: coverpoint insn_data[29:25] { bins extremes[] = {'0, '1}; }
    st_cp: coverpoint insn_data[30];
    fg_cp: coverpoint insn_data[31];
  endgroup

  covergroup enc_bnaq_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    // Used for BN.MULQACC
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_mulqacc);
      illegal_bins other = default;
    }

    za_cp: coverpoint insn_data[12];
    shift_cp: coverpoint insn_data[14:13] { bins extremes[] = {'0, '1}; }
    q1_cp: coverpoint insn_data[26:25] { bins extremes[] = {'0, '1}; }
    q2_cp: coverpoint insn_data[28:27] { bins extremes[] = {'0, '1}; }
  endgroup

  covergroup enc_bnaqs_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    // Used for BN.MULQACC.SO
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_mulqacc_so);
      illegal_bins other = default;
    }

    za_cp: coverpoint insn_data[12];
    shift_cp: coverpoint insn_data[14:13] { bins extremes[] = {'0, '1}; }
    q1_cp: coverpoint insn_data[26:25] { bins extremes[] = {'0, '1}; }
    q2_cp: coverpoint insn_data[28:27] { bins extremes[] = {'0, '1}; }
    dh_cp: coverpoint insn_data[29];
    fg_cp: coverpoint insn_data[31];
  endgroup

  covergroup enc_bnaqw_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    // Used for BN.MULQACC.WO
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_mulqacc_wo);
      illegal_bins other = default;
    }

    za_cp: coverpoint insn_data[12];
    shift_cp: coverpoint insn_data[14:13] { bins extremes[] = {'0, '1}; }
    q1_cp: coverpoint insn_data[26:25] { bins extremes[] = {'0, '1}; }
    q2_cp: coverpoint insn_data[28:27] { bins extremes[] = {'0, '1}; }
    fg_cp: coverpoint insn_data[31];
  endgroup

  covergroup enc_bnc_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_cmp);
      `DEF_MNEM_BIN(mnem_bn_cmpb);
      illegal_bins other = default;
    }

    sb_cp: coverpoint insn_data[29:25] { bins extremes[] = {'0, '1}; }
    st_cp: coverpoint insn_data[30];
    fg_cp: coverpoint insn_data[31];

    `DEF_MNEM_CROSS(sb)
    `DEF_MNEM_CROSS(st)
    `DEF_MNEM_CROSS(fg)
  endgroup

  covergroup enc_bnmov_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_mov);
      illegal_bins other = default;
    }

  endgroup

  covergroup enc_bnmovr_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_movr);
      illegal_bins other = default;
    }

    grd_inc_cp: coverpoint insn_data[7];
    grs_inc_cp: coverpoint insn_data[9];

    `DEF_GPR_CP(grs_cp, 19:15)
    `DEF_GPR_CP(grd_cp, 24:20)
    `DEF_MNEM_CROSS2(grs, grd)
  endgroup

  covergroup enc_bnr_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_rshi);
      illegal_bins other = default;
    }

    imm_cp: coverpoint {insn_data[31:25], insn_data[14]} { bins extremes[] = {'0, '1}; }
  endgroup

  covergroup enc_bns_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_sel);
      illegal_bins other = default;
    }

    flag_cp: coverpoint insn_data[26:25] { bins extremes[] = {'0, '1}; }
    fg_cp: coverpoint insn_data[31];
  endgroup

  covergroup enc_bnxid_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_lid);
      `DEF_MNEM_BIN(mnem_bn_sid);
      illegal_bins other = default;
    }

    incd_cp: coverpoint insn_data[7];
    inc1_cp: coverpoint insn_data[8];
    off_cp: coverpoint {insn_data[31:25], insn_data[11:9]} { bins extremes[] = {'0, '1}; }

    `DEF_GPR_CP(grs1_cp, 19:15)
    // Note: Bits 24:20 are called grd for BN.LID or grs2 for BN.SID, but both are a GPR, so can be
    //       tracked the same here.
    `DEF_GPR_CP(grx_cp, 24:20)

    `DEF_MNEM_CROSS(incd)
    `DEF_MNEM_CROSS(inc1)
    `DEF_MNEM_CROSS(off)

    `DEF_MNEM_CROSS2(grs1, grx)
  endgroup

  covergroup enc_b_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_beq);
      `DEF_MNEM_BIN(mnem_bne);
      illegal_bins other = default;
    }

    off_cp: coverpoint {insn_data[31], insn_data[7], insn_data[30:25], insn_data[11:8]} {
      bins extremes[] = {12'h800, 12'h7ff};
    }

    `DEF_GPR_CP(grs1_cp, 19:15)
    `DEF_GPR_CP(grs2_cp, 24:20)

    `DEF_MNEM_CROSS(off)

    `DEF_MNEM_CROSS2(grs1, grs2)
  endgroup

  covergroup enc_fixed_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    // Used for instructions (ECALL) with no immediate or register operands
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_ecall);
      illegal_bins other = default;
    }
  endgroup

  covergroup enc_i_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_addi);
      `DEF_MNEM_BIN(mnem_andi);
      `DEF_MNEM_BIN(mnem_ori);
      `DEF_MNEM_BIN(mnem_xori);
      `DEF_MNEM_BIN(mnem_lw);
      `DEF_MNEM_BIN(mnem_jalr);
      `DEF_MNEM_BIN(mnem_csrrs);
      `DEF_MNEM_BIN(mnem_csrrw);
      illegal_bins other = default;
    }

    imm_cp: coverpoint insn_data[31:20] { bins extremes[] = {12'h800, 12'h7ff}; }

    `DEF_GPR_CP(grd_cp, 11:7)
    `DEF_GPR_CP(grs1_cp, 19:15)

    `DEF_MNEM_CROSS(imm)

    `DEF_MNEM_CROSS2(grd, grs1)
  endgroup

  covergroup enc_is_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    // Instructions with the Is encoding
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_slli);
      `DEF_MNEM_BIN(mnem_srli);
      `DEF_MNEM_BIN(mnem_srai);
      illegal_bins other = default;
    }

    shamt_cp: coverpoint insn_data[24:20] { bins extremes[] = {'0, '1}; }

    `DEF_GPR_CP(grd_cp, 11:7)
    `DEF_GPR_CP(grs1_cp, 19:15)

    `DEF_MNEM_CROSS(shamt)

    `DEF_MNEM_CROSS2(grd, grs1)
  endgroup

  covergroup enc_j_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_jal);
      illegal_bins other = default;
    }

    off_cp: coverpoint insn_data[31:12] { bins extremes[] = {20'h80000, 20'h7ffff}; }

    `DEF_GPR_CP(grd_cp, 11:7)
  endgroup

  covergroup enc_loop_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    // Used for LOOP encoding (just the LOOP instruction)
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_loop);
      illegal_bins other = default;
    }

    sz_cp: coverpoint insn_data[31:20] { bins extremes[] = {'0, '1}; }

    `DEF_GPR_CP(grs_cp, 19:15)
  endgroup

  covergroup enc_loopi_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    // Used for LOOPI encoding (just the LOOPI instruction)
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_loopi);
      illegal_bins other = default;
    }

    sz_cp: coverpoint insn_data[31:20] { bins extremes[] = {'0, '1}; }
    iterations_cp: coverpoint {insn_data[19:15], insn_data[11:7]} { bins extremes[] = {'0, '1}; }
  endgroup

  covergroup enc_r_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_add);
      `DEF_MNEM_BIN(mnem_sub);
      `DEF_MNEM_BIN(mnem_sll);
      `DEF_MNEM_BIN(mnem_srl);
      `DEF_MNEM_BIN(mnem_sra);
      `DEF_MNEM_BIN(mnem_and);
      `DEF_MNEM_BIN(mnem_or);
      `DEF_MNEM_BIN(mnem_xor);
      illegal_bins other = default;
    }

    `DEF_GPR_CP(grd_cp, 11:7)
    `DEF_GPR_CP(grs1_cp, 19:15)
    `DEF_GPR_CP(grs2_cp, 24:20)

    `DEF_MNEM_CROSS3(grd, grs1, grs2)
  endgroup

  covergroup enc_s_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_sw);
      illegal_bins other = default;
    }

    off_cp: coverpoint {insn_data[31:25], insn_data[11:7]} {
      bins extremes[] = {12'h800, 12'h7ff};
    }

    `DEF_GPR_CP(grs1_cp, 19:15)
    `DEF_GPR_CP(grs2_cp, 24:20)
    `DEF_MNEM_CROSS2(grs1, grs2)
  endgroup

  covergroup enc_u_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_lui);
      illegal_bins other = default;
    }

    imm_cp: coverpoint insn_data[31:12] { bins extremes[] = {'0, '1}; }

    `DEF_GPR_CP(grd_cp, 11:7)
  endgroup

  covergroup enc_wcsr_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_wsrr);
      `DEF_MNEM_BIN(mnem_bn_wsrw);
      illegal_bins other = default;
    }

    wsr_cp: coverpoint insn_data[27:20] { bins extremes[] = {'0, '1}; }
    `DEF_MNEM_CROSS(wsr)
  endgroup

  // A mapping from instruction name to the name of that instruction's encoding.
  string insn_encodings[mnem_str_t];

  function new(string name, uvm_component parent);
    super.new(name, parent);

    enc_bna_cg = new;
    enc_bnai_cg = new;
    enc_bnam_cg = new;
    enc_bnan_cg = new;
    enc_bnaq_cg = new;
    enc_bnaqw_cg = new;
    enc_bnaqs_cg = new;
    enc_bnc_cg = new;
    enc_bnmov_cg = new;
    enc_bnmovr_cg = new;
    enc_bnr_cg = new;
    enc_bns_cg = new;
    enc_bnxid_cg = new;
    enc_b_cg = new;
    enc_fixed_cg = new;
    enc_i_cg = new;
    enc_is_cg = new;
    enc_j_cg = new;
    enc_loop_cg = new;
    enc_loopi_cg = new;
    enc_r_cg = new;
    enc_s_cg = new;
    enc_wcsr_cg = new;
    enc_u_cg = new;

    // Set up instruction encoding mapping
    insn_encodings[mnem_add]           = "R";
    insn_encodings[mnem_addi]          = "I";
    insn_encodings[mnem_lui]           = "U";
    insn_encodings[mnem_sub]           = "R";
    insn_encodings[mnem_sll]           = "R";
    insn_encodings[mnem_slli]          = "Is";
    insn_encodings[mnem_srl]           = "R";
    insn_encodings[mnem_srli]          = "Is";
    insn_encodings[mnem_sra]           = "R";
    insn_encodings[mnem_srai]          = "Is";
    insn_encodings[mnem_and]           = "R";
    insn_encodings[mnem_andi]          = "I";
    insn_encodings[mnem_or]            = "R";
    insn_encodings[mnem_ori]           = "I";
    insn_encodings[mnem_xor]           = "R";
    insn_encodings[mnem_xori]          = "I";
    insn_encodings[mnem_lw]            = "I";
    insn_encodings[mnem_sw]            = "S";
    insn_encodings[mnem_beq]           = "B";
    insn_encodings[mnem_bne]           = "B";
    insn_encodings[mnem_jal]           = "J";
    insn_encodings[mnem_jalr]          = "I";
    insn_encodings[mnem_csrrs]         = "I";
    insn_encodings[mnem_csrrw]         = "I";
    insn_encodings[mnem_ecall]         = "fixed";
    insn_encodings[mnem_loop]          = "loop";
    insn_encodings[mnem_loopi]         = "loopi";
    insn_encodings[mnem_bn_add]        = "bnaf";
    insn_encodings[mnem_bn_addc]       = "bnaf";
    insn_encodings[mnem_bn_addi]       = "bnai";
    insn_encodings[mnem_bn_addm]       = "bnam";
    insn_encodings[mnem_bn_mulqacc]    = "bnaq";
    insn_encodings[mnem_bn_mulqacc_wo] = "bnaqw";
    insn_encodings[mnem_bn_mulqacc_so] = "bnaqs";
    insn_encodings[mnem_bn_sub]        = "bnaf";
    insn_encodings[mnem_bn_subb]       = "bnaf";
    insn_encodings[mnem_bn_subi]       = "bnai";
    insn_encodings[mnem_bn_subm]       = "bnam";
    insn_encodings[mnem_bn_and]        = "bna";
    insn_encodings[mnem_bn_or]         = "bna";
    insn_encodings[mnem_bn_not]        = "bnan";
    insn_encodings[mnem_bn_xor]        = "bna";
    insn_encodings[mnem_bn_rshi]       = "bnr";
    insn_encodings[mnem_bn_sel]        = "bns";
    insn_encodings[mnem_bn_cmp]        = "bnc";
    insn_encodings[mnem_bn_cmpb]       = "bnc";
    insn_encodings[mnem_bn_lid]        = "bnxid";
    insn_encodings[mnem_bn_sid]        = "bnxid";
    insn_encodings[mnem_bn_mov]        = "bnmov";
    insn_encodings[mnem_bn_movr]       = "bnmovr";
    insn_encodings[mnem_bn_wsrr]       = "wcsr";
    insn_encodings[mnem_bn_wsrw]       = "wcsr";
  endfunction

  // Handle coverage for an instruction that was executed
  //
  // Almost all the tracking is done based on rtl_item, which comes from the DUT. Our only use for
  // iss_item is to extract the instruction mnemonic (to avoid needing it, we'd have to implement a
  // decoder in the coverage code, which doesn't seem like the right thing to do).
  //
  function void on_insn(otbn_model_item iss_item, otbn_trace_item rtl_item);
    string encoding;

    mnem_str_t   mnem;
    logic [31:0] insn_data;

    // Since iss_item and rtl_item have come in separately, we do a quick check here to make sure
    // they actually match the same instruction.
    `DV_CHECK_EQ(iss_item.insn_addr, rtl_item.insn_addr)

    // iss_item.mnemonic is a "string". We have to cast this to an integral type (mnem_str_t) to use
    // it for bins in a coverpoint. This type is chosen to be long enough to hold each valid
    // mnemonic, but it can't hurt to make absolutely sure that nothing overflows.
    `DV_CHECK_FATAL(iss_item.mnemonic.len() <= MNEM_STR_LEN)

    mnem = mnem_str_t'(iss_item.mnemonic);
    insn_data = rtl_item.insn_data;

    // Per-encoding coverage. First, use insn_encodings to find the encoding for the instruction.
    // Every instruction mnemonic should have an associated encoding schema.
    encoding = insn_encodings[mnem];
    case (encoding)
      "bna", "bnaf": enc_bna_cg.sample(mnem, insn_data);
      "bnai": enc_bnai_cg.sample(mnem, insn_data);
      "bnam": enc_bnam_cg.sample(mnem, insn_data);
      "bnaq": enc_bnaq_cg.sample(mnem, insn_data);
      "bnaqw": enc_bnaqw_cg.sample(mnem, insn_data);
      "bnaqs": enc_bnaqs_cg.sample(mnem, insn_data);
      "bnc": enc_bnc_cg.sample(mnem, insn_data);
      "bnmov": enc_bnmov_cg.sample(mnem, insn_data);
      "bnmovr": enc_bnmovr_cg.sample(mnem, insn_data);
      "bnr": enc_bnr_cg.sample(mnem, insn_data);
      "bns": enc_bns_cg.sample(mnem, insn_data);
      "bnxid": enc_bnxid_cg.sample(mnem, insn_data);
      "B": enc_b_cg.sample(mnem, insn_data);
      "fixed": enc_fixed_cg.sample(mnem, insn_data);
      "I": enc_i_cg.sample(mnem, insn_data);
      "Is": enc_is_cg.sample(mnem, insn_data);
      "J": enc_j_cg.sample(mnem, insn_data);
      "loop": enc_loop_cg.sample(mnem, insn_data);
      "loopi": enc_loopi_cg.sample(mnem, insn_data);
      "R": enc_r_cg.sample(mnem, insn_data);
      "S": enc_s_cg.sample(mnem, insn_data);
      "U": enc_u_cg.sample(mnem, insn_data);
      "wcsr": enc_wcsr_cg.sample(mnem, insn_data);
      default: `DV_CHECK_FATAL(0, "Unknown encoding")
    endcase
  endfunction

`undef DEF_MNEM_BIN
`undef DEF_MNEM_CROSS
`undef DEF_MNEM_CROSS2
`undef DEF_MNEM_CROSS3
`undef GPR_BIN_TYPES
`undef DEF_GPR_CP

endclass
