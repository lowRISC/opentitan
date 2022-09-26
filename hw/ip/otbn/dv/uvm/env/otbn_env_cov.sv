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
  // A fake mnemonic, used for bits that don't decode to a real instruction
  `DEF_MNEM(mnem_dummy,         "dummy-insn");
  // A fake mnemonic, used for invalid IMEM data (after a failed integrity check)
  `DEF_MNEM(mnem_question_mark, "??");
`undef DEF_MNEM

  // A macro used for coverpoints for mnemonics. This expands to entries like
  //
  //    bins mnem_add = {mnem_add};
`define DEF_MNEM_BIN(NAME) bins NAME = {NAME}

  // Generate a bin for each mnemonic except ECALL
`define DEF_MNEM_BINS_EXCEPT_ECALL                                     \
    `DEF_MNEM_BIN(mnem_add); `DEF_MNEM_BIN(mnem_addi);                 \
    `DEF_MNEM_BIN(mnem_lui); `DEF_MNEM_BIN(mnem_sub);                  \
    `DEF_MNEM_BIN(mnem_sll); `DEF_MNEM_BIN(mnem_slli);                 \
    `DEF_MNEM_BIN(mnem_srl); `DEF_MNEM_BIN(mnem_srli);                 \
    `DEF_MNEM_BIN(mnem_sra); `DEF_MNEM_BIN(mnem_srai);                 \
    `DEF_MNEM_BIN(mnem_and); `DEF_MNEM_BIN(mnem_andi);                 \
    `DEF_MNEM_BIN(mnem_or); `DEF_MNEM_BIN(mnem_ori);                   \
    `DEF_MNEM_BIN(mnem_xor); `DEF_MNEM_BIN(mnem_xori);                 \
    `DEF_MNEM_BIN(mnem_lw); `DEF_MNEM_BIN(mnem_sw);                    \
    `DEF_MNEM_BIN(mnem_beq); `DEF_MNEM_BIN(mnem_bne);                  \
    `DEF_MNEM_BIN(mnem_jal); `DEF_MNEM_BIN(mnem_jalr);                 \
    `DEF_MNEM_BIN(mnem_csrrs); `DEF_MNEM_BIN(mnem_csrrw);              \
    `DEF_MNEM_BIN(mnem_loop); `DEF_MNEM_BIN(mnem_loopi);               \
    `DEF_MNEM_BIN(mnem_bn_add); `DEF_MNEM_BIN(mnem_bn_addc);           \
    `DEF_MNEM_BIN(mnem_bn_addi); `DEF_MNEM_BIN(mnem_bn_addm);          \
    `DEF_MNEM_BIN(mnem_bn_mulqacc); `DEF_MNEM_BIN(mnem_bn_mulqacc_wo); \
    `DEF_MNEM_BIN(mnem_bn_mulqacc_so);                                 \
    `DEF_MNEM_BIN(mnem_bn_sub); `DEF_MNEM_BIN(mnem_bn_subb);           \
    `DEF_MNEM_BIN(mnem_bn_subi); `DEF_MNEM_BIN(mnem_bn_subm);          \
    `DEF_MNEM_BIN(mnem_bn_and); `DEF_MNEM_BIN(mnem_bn_or);             \
    `DEF_MNEM_BIN(mnem_bn_not); `DEF_MNEM_BIN(mnem_bn_xor);            \
    `DEF_MNEM_BIN(mnem_bn_rshi);                                       \
    `DEF_MNEM_BIN(mnem_bn_sel);                                        \
    `DEF_MNEM_BIN(mnem_bn_cmp); `DEF_MNEM_BIN(mnem_bn_cmpb);           \
    `DEF_MNEM_BIN(mnem_bn_lid); `DEF_MNEM_BIN(mnem_bn_sid);            \
    `DEF_MNEM_BIN(mnem_bn_mov); `DEF_MNEM_BIN(mnem_bn_movr);           \
    `DEF_MNEM_BIN(mnem_bn_wsrr); `DEF_MNEM_BIN(mnem_bn_wsrw);

  // Equivalents of DEF_MNEM and DEF_MNEM_BINp, but for external CSRs. Again, we want to use the CSR
  // names as bins in coverpoints and need sized literals.
`define DEF_CSR(CSR_NAME, STR) \
  csr_str_t CSR_NAME = csr_str_t'(STR)
  `DEF_CSR(csr_load_checksum, "load_checksum");
  `DEF_CSR(csr_ctrl, "ctrl");
`undef DEF_CSR
`define DEF_CSR_BIN(NAME) bins NAME = {NAME}

  // Cross one, two or three coverpoints with mnemonic_cp.
  //
  // This is intentended to be used inside covergroups that support multiple instructions. In each
  // of these, we define a coverpoint called mnemonic_cp to track which instruction is being
  // sampled.
`define DEF_MNEM_CROSS(BASENAME)                                         \
    BASENAME``_cross: cross mnemonic_cp, BASENAME``_cp;
`define DEF_MNEM_CROSS2(BASE0, BASE1)                                    \
    BASE0``_``BASE1``_cross: cross mnemonic_cp, BASE0``_cp, BASE1``_cp;
`define DEF_MNEM_CROSS3(BASE0, BASE1, BASE2)                             \
    BASE0``_``BASE1``_``BASE2``_cross:                                   \
      cross mnemonic_cp, BASE0``_cp, BASE1``_cp, BASE2``_cp;

  // A macro to define bins for GPR types. The point is that there are 3 interesting types of GPR:
  // x0, x1 and everything else.
`define GPR_BIN_TYPES \
  { bins gpr_x0 = {5'd0}; bins gpr_x1 = {5'd1}; bins gpr_other = {[5'd2:$]}; }

  // Declare a GPR coverpoint with the 3 types above
`define DEF_GPR_CP(NAME, BITS) \
  NAME: coverpoint insn_data[BITS] `GPR_BIN_TYPES

  // Macros for tracking "toggle coverage" of some bitfield. Use one of the DEF_*_TOGGLE_COV macros
  // to define a coverpoint for each bit of the bitfield.
  //
  // The implementation uses macros to expand in powers of 2. The trick is that BIN_IDX will grow to
  // give the base-2 representation of the index of the bit we're looking at. For example, the
  // expansion of DEF_GPR_TOGGLE_COV(NAME, x) ends up with 32 calls to _DEF_TOGGLE_COV_1:
  //
  //    _DEF_TOGGLE_COV_1(NAME, x, 5, 00000)
  //    ...
  //    _DEF_TOGGLE_COV_1(NAME, x, 5, 11111)
  //
  // This, in turn, expands to
  //
  //    NAME_00000_cp: coverpoint x[5'b00000];
  //    ...
  //    NAME_11111_cp: coverpoint x[5'b11111];
  //
  // to track the 32 bits in x.
  //
`define _DEF_TOGGLE_COV_1(BASE, BITS, IDXW, BIN_IDX)        \
  BASE``_``BIN_IDX``_cp: coverpoint BITS[IDXW 'b BIN_IDX];
`define _DEF_TOGGLE_COV_2(BASE, BITS, IDXW, BIN_IDX)        \
  `_DEF_TOGGLE_COV_1(BASE, BITS, IDXW, BIN_IDX``0)          \
  `_DEF_TOGGLE_COV_1(BASE, BITS, IDXW, BIN_IDX``1)
`define _DEF_TOGGLE_COV_4(BASE, BITS, IDXW, BIN_IDX)        \
  `_DEF_TOGGLE_COV_2(BASE, BITS, IDXW, BIN_IDX``0)          \
  `_DEF_TOGGLE_COV_2(BASE, BITS, IDXW, BIN_IDX``1)
`define _DEF_TOGGLE_COV_8(BASE, BITS, IDXW, BIN_IDX)        \
  `_DEF_TOGGLE_COV_4(BASE, BITS, IDXW, BIN_IDX``0)          \
  `_DEF_TOGGLE_COV_4(BASE, BITS, IDXW, BIN_IDX``1)
`define _DEF_TOGGLE_COV_16(BASE, BITS, IDXW, BIN_IDX)       \
  `_DEF_TOGGLE_COV_8(BASE, BITS, IDXW, BIN_IDX``0)          \
  `_DEF_TOGGLE_COV_8(BASE, BITS, IDXW, BIN_IDX``1)
`define _DEF_TOGGLE_COV_32(BASE, BITS, IDXW, BIN_IDX)       \
  `_DEF_TOGGLE_COV_16(BASE, BITS, IDXW, BIN_IDX``0)         \
  `_DEF_TOGGLE_COV_16(BASE, BITS, IDXW, BIN_IDX``1)
`define _DEF_TOGGLE_COV_64(BASE, BITS, IDXW, BIN_IDX)       \
  `_DEF_TOGGLE_COV_32(BASE, BITS, IDXW, BIN_IDX``0)         \
  `_DEF_TOGGLE_COV_32(BASE, BITS, IDXW, BIN_IDX``1)
`define _DEF_TOGGLE_COV_128(BASE, BITS, IDXW, BIN_IDX)      \
  `_DEF_TOGGLE_COV_64(BASE, BITS, IDXW, BIN_IDX``0)         \
  `_DEF_TOGGLE_COV_64(BASE, BITS, IDXW, BIN_IDX``1)

`define DEF_GPR_TOGGLE_COV(BASE, BITS)                      \
  `_DEF_TOGGLE_COV_16(BASE, BITS, 5, 0)                     \
  `_DEF_TOGGLE_COV_16(BASE, BITS, 5, 1)
`define DEF_WDR_TOGGLE_COV(BASE, BITS)                      \
  `_DEF_TOGGLE_COV_128(BASE, BITS, 8, 0)                    \
  `_DEF_TOGGLE_COV_128(BASE, BITS, 8, 1)
`define DEF_FLAGS_TOGGLE_COV(BASE, BITS)                    \
  `_DEF_TOGGLE_COV_2(BASE, BITS, 2, 0)                      \
  `_DEF_TOGGLE_COV_2(BASE, BITS, 2, 1)
`define DEF_MLZ_FLAGS_TOGGLE_COV(BASE, BITS)                \
  `_DEF_TOGGLE_COV_1(BASE, BITS, 2, 01)                     \
  `_DEF_TOGGLE_COV_2(BASE, BITS, 2, 1)

  // Macros to allow crossing the "toggle" coverpoints defined by the previous macros with the
  // mnemonic coverpoint for some encoding schema. These work just as above and the entry points to
  // use are DEF_*_TOGGLE_CROSS.
  //
  // The DEF_*_TOGGLE_COV macros above define coverpoints with names like XXX_BBBB_cp. These macros
  // define crosses with names XXX_BBBB_cross.
`define _DEF_TOGGLE_CROSS_1(BASE, BIN_IDX)                              \
  BASE``_``BIN_IDX``_cross: cross mnemonic_cp, BASE``_``BIN_IDX``_cp;
`define _DEF_TOGGLE_CROSS_2(BASE, BIN_IDX)                              \
  `_DEF_TOGGLE_CROSS_1(BASE, BIN_IDX``0)                                \
  `_DEF_TOGGLE_CROSS_1(BASE, BIN_IDX``1)
`define _DEF_TOGGLE_CROSS_4(BASE, BIN_IDX)                              \
  `_DEF_TOGGLE_CROSS_2(BASE, BIN_IDX``0)                                \
  `_DEF_TOGGLE_CROSS_2(BASE, BIN_IDX``1)
`define _DEF_TOGGLE_CROSS_8(BASE, BIN_IDX)                              \
  `_DEF_TOGGLE_CROSS_4(BASE, BIN_IDX``0)                                \
  `_DEF_TOGGLE_CROSS_4(BASE, BIN_IDX``1)
`define _DEF_TOGGLE_CROSS_16(BASE, BIN_IDX)                             \
  `_DEF_TOGGLE_CROSS_8(BASE, BIN_IDX``0)                                \
  `_DEF_TOGGLE_CROSS_8(BASE, BIN_IDX``1)
`define _DEF_TOGGLE_CROSS_32(BASE, BIN_IDX)                             \
  `_DEF_TOGGLE_CROSS_16(BASE, BIN_IDX``0)                               \
  `_DEF_TOGGLE_CROSS_16(BASE, BIN_IDX``1)
`define _DEF_TOGGLE_CROSS_64(BASE, BIN_IDX)                             \
  `_DEF_TOGGLE_CROSS_32(BASE, BIN_IDX``0)                               \
  `_DEF_TOGGLE_CROSS_32(BASE, BIN_IDX``1)
`define _DEF_TOGGLE_CROSS_128(BASE, BIN_IDX)                            \
  `_DEF_TOGGLE_CROSS_64(BASE, BIN_IDX``0)                               \
  `_DEF_TOGGLE_CROSS_64(BASE, BIN_IDX``1)

`define DEF_GPR_TOGGLE_CROSS(BASE)                                      \
  `_DEF_TOGGLE_CROSS_16(BASE, 0)                                        \
  `_DEF_TOGGLE_CROSS_16(BASE, 1)
`define DEF_WDR_TOGGLE_CROSS(BASE)                                      \
  `_DEF_TOGGLE_CROSS_128(BASE, 0)                                       \
  `_DEF_TOGGLE_CROSS_128(BASE, 1)
`define DEF_FLAGS_TOGGLE_CROSS(BASE)                                    \
  `_DEF_TOGGLE_CROSS_2(BASE, 0)                                         \
  `_DEF_TOGGLE_CROSS_2(BASE, 1)
`define DEF_MLZ_FLAGS_TOGGLE_CROSS(BASE)                                \
  `_DEF_TOGGLE_CROSS_1(BASE, 01)                                        \
  `_DEF_TOGGLE_CROSS_2(BASE, 1)

  // A macro to define a coverpoint based on the sign of a value (assumed to be represented by an
  // unsigned SystemVerilog expression).
`define DEF_SIGN_CP(NAME, VALUE, WIDTH)           \
  NAME: coverpoint VALUE {                        \
    bins zero = {0};                              \
    bins pos = {[1:(WIDTH'd1 << (WIDTH - 1))-1]}; \
    bins neg = {[WIDTH'd1 << (WIDTH - 1):$]};     \
  }

  // The bins for a coverpoint that checks whether a value is zero or not (assumed to be represented
  // by an unsigned SystemVerilog expression). Used by DEF_NZ_CP and DEF_NZ_IF_CP.
`define _NZ_CP_BINS {       \
    bins zero = {0};        \
    bins nonzero = {[1:$]}; \
  }

  // A macro to define a coverpoint based on whether a value is zero or not (assumed to be
  // represented by an unsigned SystemVerilog expression).
`define DEF_NZ_CP(NAME, VALUE) NAME: coverpoint VALUE `_NZ_CP_BINS

  // A macro to define a coverpoint for a condition that should be seen: EXPR should be a single bit
  // and there's just one bin (with expected value 1'b1).
`define DEF_SEEN_CP(NAME, EXPR) NAME: coverpoint (EXPR) { bins seen = {1'b1}; }

  // Equivalent of DEF_NZ_CP and DEF_SEEN_CP, but which add a test to qualifies the coverpoint.
`define DEF_NZ_IF_CP(NAME, VALUE, TEST) NAME: coverpoint (VALUE) iff (TEST) `_NZ_CP_BINS
`define DEF_SEEN_IF_CP(NAME, EXPR, TEST) NAME: coverpoint (EXPR) iff (TEST) { bins seen = {1'b1}; }

  // Remap a CSR index to an internal "coverage" index. This function avoids having to duplicate the
  // list of CSRs below and is also an easy way to explicitly track invalid CSRs explicitly
  // (SystemVerilog doesn't provide a helpful "catch anything else" bin because 'default' doesn't
  // get included in crosses).
  //
  // Use it by calling DEF_CSR_CP, which uses remap_csr to map to bins and then undoes the mapping
  // again (now that all invalid CSRs have been squashed together) to give decent bin names.
  function int remap_csr(logic [11:0] csr_idx);
    case (csr_idx)
      12'h7c0: return 0;   // FG0
      12'h7c1: return 1;   // FG1
      12'h7c8: return 2;   // FLAGS
      12'h7d0: return 3;   // MOD0
      12'h7d1: return 4;   // MOD1
      12'h7d2: return 5;   // MOD2
      12'h7d3: return 6;   // MOD3
      12'h7d4: return 7;   // MOD4
      12'h7d5: return 8;   // MOD5
      12'h7d6: return 9;   // MOD6
      12'h7d7: return 10;  // MOD7
      12'hfc8: return 11;  // RND_PREFETCH
      12'hfc0: return 12;  // RND
      12'hfc1: return 13;  // URND
      default: return -1;  // (invalid)
    endcase
  endfunction

`define DEF_CSR_CP(NAME, EXPR)         \
  NAME: coverpoint (remap_csr(EXPR)) { \
    bins fg0          = {0};           \
    bins fg1          = {1};           \
    bins flags        = {2};           \
    bins mod0         = {3};           \
    bins mod1         = {4};           \
    bins mod2         = {5};           \
    bins mod3         = {6};           \
    bins mod4         = {7};           \
    bins mod5         = {8};           \
    bins mod6         = {9};           \
    bins mod7         = {10};          \
    bins rnd_prefetch = {11};          \
    bins rnd          = {12};          \
    bins urnd         = {13};          \
    bins invalid      = {-1};          \
    illegal_bins bad  = default;       \
  }

  // An equivalent of remap_csr / DEF_CSR_CP, but specialized to WSRs.
  function int remap_wsr(logic [7:0] wsr_idx);
    case (wsr_idx)
      8'h00: return 0;     // MOD
      8'h01: return 1;     // RND
      8'h02: return 2;     // URND
      8'h03: return 3;     // ACC
      8'h04: return 4;     // KEY_S0_L
      8'h05: return 5;     // KEY_S0_H
      8'h06: return 6;     // KEY_S1_L
      8'h07: return 7;     // KEY_S1_H
      default: return -1;  // (invalid)
    endcase
  endfunction

`define DEF_WSR_CP(NAME, EXPR)         \
  NAME: coverpoint (remap_wsr(EXPR)) { \
    bins mod         = {0};            \
    bins rnd         = {1};            \
    bins urnd        = {2};            \
    bins acc         = {3};            \
    bins key_s0_l    = {4};            \
    bins key_s0_h    = {5};            \
    bins key_s1_l    = {6};            \
    bins key_s1_h    = {7};            \
    bins invalid     = {-1};           \
    illegal_bins bad = default;        \
  }

  // State tracking

  // For the LOAD_CHECKSUM CSR, we want to see the following sequence: write the CSR; perform at
  // least one memory update; read the CSR. It's a little awkward to encode this with SystemVerilog
  // functional coverage, so we cheat and put the temporal logic into a little "fsm state" here.
  // This is updated in on_ext_csr_access() (when accessing the right CSR) and in on_mem_write.
  typedef enum {
    WUR_IDLE,
    WUR_WRITTEN_CSR,  // We've seen a write to the LOAD_CHECKSUM CSR
    WUR_UPDATED_MEM   // And now we've seen a write that updates memory
  } load_checksum_write_upd_read_e;

  load_checksum_write_upd_read_e wur_state;

  // For some CSRs, we want to see a write to the CSR in each operational state, followed by a read
  // before the next write (although it's ok if we've changed operational state since). To track
  // this, we keep an associative array keyed by CSR name whose value is the last operational state
  // where we've seen a write that changes the value. If there is a value at the name when we read
  // the CSR, we sample the ext_csr_wr_operational_state_cg covergroup.
  operational_state_e last_write_state[csr_str_t];

  // To track "error promotion" based on the CTRL register, we want to see each software error cause
  // a fatal alert. One way to do this is to run a test, check we're in the LOCKED state, then look
  // at ERR_BITS and see just one SW error, then look at FATAL_ALERT_CAUSE and see that only the
  // FATAL_SOFTWARE bit is set.
  //
  // Of course, this is a bit fiddly to track because there are several things that have to happen
  // in order. This variable gets set on each read of ERR_BITS and cleared on reset or on a change
  // of operational state. The idea is that if we read FATAL_ALERT_CAUSE and see only FATAL_SOFTWARE
  // set then we can sample the promoted_err_cg covergroup, tracking which SW error was promoted.
  // Clearing when when changing operational state makes sure that we really have seen nonzero
  // ERR_BITS since the last operation finished.
  logic [31:0] last_err_bits = 0;

  // The last mnemonic that we saw. Used to implement the pairwise mnemonic covergroup. Gets
  // initialised to 0 (not a valid mnemonic!)
  mnem_str_t last_mnem = '0;

  // Non-core covergroups //////////////////////////////////////////////////////

  // CMD external CSR
  covergroup ext_csr_cmd_cg
    with function sample(otbn_pkg::cmd_e     value,
                         access_e            access_type,
                         operational_state_e state);

    // Expect to see each genuine command, plus at least one bogus value
    cmd_cp: coverpoint {value} {
      bins CmdExecute     = {otbn_pkg::CmdExecute};
      bins CmdSecWipeDmem = {otbn_pkg::CmdSecWipeDmem};
      bins CmdSecWipeImem = {otbn_pkg::CmdSecWipeImem};
      bins BogusCmd       = {[0:$]} with (!(item inside {otbn_pkg::CmdExecute,
                                                         otbn_pkg::CmdSecWipeDmem,
                                                         otbn_pkg::CmdSecWipeImem}));
    }
    access_type_cp: coverpoint access_type;

    // We want to see an attempt to issue every command in every state.
    cmd_state_cross: cross cmd_cp, state iff (access_type == AccessSoftwareWrite);

  endgroup

  // CTRL external CSR
  covergroup ext_csr_ctrl_cg
    with function sample(logic               value,
                         access_e            access_type,
                         operational_state_e state);
    // See a read as well as a write.
    access_type_cp: coverpoint access_type;

    // See a write of each value in idle state.
    value_cp: coverpoint value iff ((access_type == AccessSoftwareWrite) &&
                                    (state == OperationalStateIdle));
  endgroup

  // STATUS external CSR
  covergroup ext_csr_status_cg
    with function sample(otbn_pkg::status_e  value,
                         access_e            access_type);
    // Read each possible status value
    status_cp: coverpoint value iff (access_type == AccessSoftwareRead);

    // See a write as well as a read.
    access_type_cp: coverpoint access_type;
  endgroup

  // ERR_BITS external CSR
  covergroup ext_csr_err_bits_cg
    with function sample(otbn_pkg::err_bits_t value,
                         logic [31:0]         old_value,
                         access_e             access_type,
                         operational_state_e  state);
    // We want to read every error bit at least once.
`define DEF_ERR_BIT_CP(NAME) \
  `DEF_SEEN_IF_CP(err_bits_``NAME``_cp, value.NAME, access_type == AccessSoftwareRead)

    `DEF_ERR_BIT_CP(bad_insn_addr)
    `DEF_ERR_BIT_CP(bad_data_addr)
    `DEF_ERR_BIT_CP(call_stack)
    `DEF_ERR_BIT_CP(illegal_insn)
    `DEF_ERR_BIT_CP(loop)
    `DEF_ERR_BIT_CP(key_invalid)
    `DEF_ERR_BIT_CP(rnd_rep_chk_fail)
    `DEF_ERR_BIT_CP(rnd_fips_chk_fail)
    `DEF_ERR_BIT_CP(imem_intg_violation)
    `DEF_ERR_BIT_CP(dmem_intg_violation)
    `DEF_ERR_BIT_CP(reg_intg_violation)
    `DEF_ERR_BIT_CP(bus_intg_violation)
    `DEF_ERR_BIT_CP(bad_internal_state)
    `DEF_ERR_BIT_CP(illegal_bus_access)
    `DEF_ERR_BIT_CP(lifecycle_escalation)
    `DEF_ERR_BIT_CP(fatal_software)

`undef DEF_ERR_BIT_CP

    // We want to see a read of ERR_BITS in every operational state, but don't need a full cross
    // with all possible error values.
    state_cp: coverpoint state iff (access_type == AccessSoftwareRead);

    // We want to track writes to ERR_BITS when the old value was nonzero.
    `DEF_SEEN_IF_CP(clear_cp, old_value != 0, access_type == AccessSoftwareWrite)

    // Cross these writes with the operational state
    clear_state_cross: cross clear_cp, state;

    // See both reads and writes. This is actually implied by clear_cp and state_cp, but it can't
    // hurt to be explicit.
    access_type_cp: coverpoint access_type;
  endgroup

  // FATAL_ALERT_CAUSE external CSR
  covergroup ext_csr_fatal_alert_cause_cg
    with function sample(logic [31:0]        value,
                         access_e            access_type,
                         operational_state_e state);

    // We want to see every valid bit at least once.
`define DEF_FAC_CP(NAME, IDX) \
  `DEF_SEEN_IF_CP(fatal_alert_cause_``NAME``_cp, value[IDX], access_type == AccessSoftwareRead)

    `DEF_FAC_CP(imem_intg_violation, 0)
    `DEF_FAC_CP(dmem_intg_violation, 1)
    `DEF_FAC_CP(reg_intg_violation, 2)
    `DEF_FAC_CP(bus_intg_violation, 3)
    `DEF_FAC_CP(bad_internal_state, 4)
    `DEF_FAC_CP(illegal_bus_access, 5)
    `DEF_FAC_CP(lifecycle_escalation, 6)
    `DEF_FAC_CP(fatal_software, 7)

`undef DEF_FAC_CP

    // We want to see a read of FATAL_ALERT_CAUSE in every operational state, but don't need to see
    // all possible values that could be read.
    state_cp: coverpoint state iff (access_type == AccessSoftwareRead);

    // See a write as well as a read.
    access_type_cp: coverpoint access_type;
  endgroup

  // INSN_CNT external CSR
  covergroup ext_csr_insn_cnt_cg
    with function sample(logic [31:0]        value,
                         logic [31:0]        old_value,
                         access_e            access_type,
                         operational_state_e state);

    // We want to see at least one non-zero value of INSN_CNT to ensure it's doing something. The
    // actual values are cross-checked with the ISS.
    `DEF_NZ_IF_CP(insn_cnt_cp, value, access_type == AccessSoftwareRead)

    // We want to see a read from INSN_CNT in all operational states
    state_cp: coverpoint state iff (access_type == AccessSoftwareRead);

    // We want to track writes to INSN_CNT the old value was nonzero.
    `DEF_SEEN_IF_CP(clear_cp, old_value != 0, access_type == AccessSoftwareWrite)

    // Cross these writes with the operational state
    clear_state_cross: cross clear_cp, state;
  endgroup

  // Specialized covergroup for LOAD_CHECKSUM external CSR. This is used to track the "write CSR;
  // write mem; read CSR" sequence. See notes above load_checksum_write_upd_read_e for more
  // information. We've seen the sequence once we call the sample function.
  covergroup ext_csr_load_checksum_wur_cg with function sample();
    `DEF_SEEN_CP(wur_cp, 1'b1)
  endgroup

  // Specialized covergroup "write then read" where we that track writes across different
  // operational states, followed by a read (to check that the write took some effect). See note
  // above last_write_state for details of how this works.
  covergroup ext_csr_wr_operational_state_cg
    with function sample(csr_str_t csr, operational_state_e wr_state);

    csr_cp: coverpoint csr {
      `DEF_CSR_BIN(csr_load_checksum);
      `DEF_CSR_BIN(csr_ctrl);
      illegal_bins other = default;
    }

    csr_state_cross: cross csr_cp, wr_state;

  endgroup

  // Specialized covergroup to track that we've seen each software error individually cause a fatal
  // alert. This gets sampled when we read a FATAL_ALERT_CAUSE with just FATAL_SOFTWARE and is given
  // last_err_bits (see comment above declaration of that variable for more details).
  covergroup promoted_err_cg
    with function sample(logic [5:0] last_err_bits);

    // We're interested in the "one-hot" values corresponding to each error that wouldn't normally
    // be fatal.
    err_bits_cp: coverpoint last_err_bits {
      bins bad_data_addr = {6'h1};
      bins bad_insn_addr = {6'h2};
      bins call_stack    = {6'h4};
      bins illegal_insn  = {6'h8};
      bins loop          = {6'h10};
      bins key_invalid   = {6'h20};
    }
  endgroup

  covergroup scratchpad_writes_cg with function sample(uvm_reg_addr_t addr);
    // See attempted writes to the bottom and top address in the scratchpad memory
    addr_cp: coverpoint addr {
      bins low  = {OTBN_DMEM_OFFSET + OTBN_DMEM_SIZE};
      bins high = {OTBN_DMEM_OFFSET + DmemSizeByte - 4};
    }
  endgroup

  // Non-instruction covergroups ///////////////////////////////////////////////

  covergroup call_stack_cg
    with function sample(call_stack_flags_t flags,
                         stack_fullness_e   fullness);

    // There are 3 different flags in flags (two "read ports" and a "write port"). Cross them to see
    // all 8 possible values.
    flags_cp: coverpoint flags;

    // 3 possible values of fullness (empty, partially full, full)
    fullness_cp: coverpoint fullness;

    // Cross push/pop behaviour with fullness of the call stack to give 8 * 3 = 24 bins.
    flags_fullness_cross: cross flags_cp, fullness_cp;

  endgroup

  covergroup flag_write_cg
    with function sample(bit     flag_group,
                         flags_t read_data,
                         flags_t write_data);

    // The following coverpoints track writes to the different flags in the flag group that set or
    // clear the flag, respectively. These are then crossed with fg_cp because we want to see each
    // event with each flag group.

    fg_cp: coverpoint flag_group;

    `DEF_SEEN_CP(set_Z_cp, write_data.Z & ~read_data.Z)
    `DEF_SEEN_CP(set_L_cp, write_data.L & ~read_data.L)
    `DEF_SEEN_CP(set_M_cp, write_data.M & ~read_data.M)
    `DEF_SEEN_CP(set_C_cp, write_data.C & ~read_data.C)

    `DEF_SEEN_CP(clr_Z_cp, read_data.Z & ~write_data.Z)
    `DEF_SEEN_CP(clr_L_cp, read_data.L & ~write_data.L)
    `DEF_SEEN_CP(clr_M_cp, read_data.M & ~write_data.M)
    `DEF_SEEN_CP(clr_C_cp, read_data.C & ~write_data.C)

    set_Z_cross: cross fg_cp, set_Z_cp;
    set_L_cross: cross fg_cp, set_L_cp;
    set_M_cross: cross fg_cp, set_M_cp;
    set_C_cross: cross fg_cp, set_C_cp;

    clr_Z_cross: cross fg_cp, clr_Z_cp;
    clr_L_cross: cross fg_cp, clr_L_cp;
    clr_M_cross: cross fg_cp, clr_M_cp;
    clr_C_cross: cross fg_cp, clr_C_cp;
  endgroup

  // This covergroup tracks each possible "Bad Internal State" fatal error
  // cause using probes from RTL.
  covergroup bad_internal_state_cg
    with function sample(logic urnd_all_zero,
                         logic insn_addr_err,
                         logic scramble_state_err,
                         otbn_pkg::predec_err_t predec_err,
                         otbn_pkg::missed_gnt_t missed_gnt,
                         otbn_pkg::controller_bad_int_t controller_bad_int,
                         otbn_pkg::start_stop_bad_int_t start_stop_bad_int,
                         logic rf_base_spurious_we_err,
                         logic rf_bignum_spurious_we_err,
                         logic ext_mubi_err);

    `DEF_SEEN_CP(alu_bignum_predec_err, predec_err.alu_bignum_err)
    `DEF_SEEN_CP(mac_bignum_predec_err, predec_err.mac_bignum_err)
    `DEF_SEEN_CP(ispr_bignum_predec_err, predec_err.ispr_bignum_err)
    `DEF_SEEN_CP(controller_predec_err, predec_err.controller_err)
    `DEF_SEEN_CP(rf_predec_err, predec_err.rf_err)
    `DEF_SEEN_CP(rd_predec_err, predec_err.rd_err)

    `DEF_SEEN_CP(spr_urnd_acks_cp, start_stop_bad_int.spr_urnd_acks)
    `DEF_SEEN_CP(spr_rnd_acks_cp, start_stop_bad_int.spr_rnd_acks)
    `DEF_SEEN_CP(spr_secwipe_reqs_cp, start_stop_bad_int.spr_secwipe_reqs)
    `DEF_SEEN_CP(mubi_rma_err_cp, start_stop_bad_int.mubi_rma_err)
    `DEF_SEEN_CP(mubi_urnd_err_cp, start_stop_bad_int.mubi_urnd_err)
    `DEF_SEEN_CP(start_stop_state_err_cp, start_stop_bad_int.state_err)

    `DEF_SEEN_CP(loop_hw_cnt_err_cp, controller_bad_int.loop_hw_cnt_err)
    `DEF_SEEN_CP(loop_hw_stack_cnt_err_cp, controller_bad_int.loop_hw_stack_cnt_err)
    `DEF_SEEN_CP(loop_hw_intg_err_cp, controller_bad_int.loop_hw_intg_err)
    `DEF_SEEN_CP(rf_base_call_stack_err_cp, controller_bad_int.rf_base_call_stack_err)
    `DEF_SEEN_CP(spr_secwipe_acks_cp, controller_bad_int.spr_secwipe_acks)
    `DEF_SEEN_CP(controller_state_err_cp, controller_bad_int.state_err)
    `DEF_SEEN_CP(controller_mubi_err_cp, controller_bad_int.controller_mubi_err)

    `DEF_SEEN_CP(imem_gnt_missed_err_cp, missed_gnt.imem_gnt_missed_err)
    `DEF_SEEN_CP(dmem_gnt_missed_err_cp, missed_gnt.dmem_gnt_missed_err)

    `DEF_SEEN_CP(urnd_all_zero_cp, urnd_all_zero)
    `DEF_SEEN_CP(insn_addr_err_cp, insn_addr_err)
    `DEF_SEEN_CP(scramble_state_err_cp, scramble_state_err)
    `DEF_SEEN_CP(rf_base_spurious_we_err_cp, rf_base_spurious_we_err)
    `DEF_SEEN_CP(rf_bignum_spurious_we_err_cp, rf_bignum_spurious_we_err)
    `DEF_SEEN_CP(ext_mubi_err_cp, ext_mubi_err)

  endgroup

  // This covergroup tracks each possible "Internal Integrity Errors" with probes from RTL.
  covergroup internal_intg_err_cg with function sample(otbn_pkg::internal_intg_err_t intg_err);

    `DEF_SEEN_CP(rf_base_intg_err_cp, intg_err.rf_base_intg_err)
    `DEF_SEEN_CP(rf_bignum_intg_err_cp, intg_err.rf_bignum_intg_err)
    `DEF_SEEN_CP(mod_ispr_intg_err_cp, intg_err.mod_ispr_intg_err)
    `DEF_SEEN_CP(acc_ispr_intg_err_cp, intg_err.acc_ispr_intg_err)
    `DEF_SEEN_CP(loop_stack_addr_intg_err_cp, intg_err.loop_stack_addr_intg_err)
    `DEF_SEEN_CP(insn_fetch_intg_err_cp, intg_err.insn_fetch_intg_err)

  endgroup

  // This covergroup tracks straight-line instructions (i.e., instructions that do not
  // branch or jump) at the top of instruction memory (i.e., at the highest possible
  // address).
  covergroup insn_addr_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_addr);
    `DEF_SEEN_CP(str_insn_at_top_cp, (insn_addr == ImemSizeByte - 4) &&
                                     !(mnemonic inside {mnem_beq, mnem_bne, mnem_jal, mnem_jalr,
                                                        mnem_ecall, mnem_loop, mnem_loopi}))

  endgroup

  // Pairwise instructions /////////////////////////////////////////////////////

  covergroup pairwise_insn_cg with function sample(mnem_str_t last, mnem_str_t cur);
    last_cp: coverpoint last {
      `DEF_MNEM_BINS_EXCEPT_ECALL
      illegal_bins other = default;
    }
    cur_cp: coverpoint cur {
      `DEF_MNEM_BINS_EXCEPT_ECALL
      `DEF_MNEM_BIN(mnem_ecall);
      `DEF_MNEM_BIN(mnem_dummy);
      `DEF_MNEM_BIN(mnem_question_mark);
      illegal_bins other = default;
    }
    pair_cross: cross last_cp, cur_cp;
  endgroup

  // Per-encoding covergroups //////////////////////////////////////////////////
  covergroup enc_bna_cg
    with function sample(mnem_str_t    mnemonic,
                         logic [31:0]  insn_data,
                         logic [255:0] wdr_operand_a,
                         logic [255:0] wdr_operand_b,
                         flags_t       flags_write_data [2],
                         logic [255:0] wdr_write_data);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_and);
      `DEF_MNEM_BIN(mnem_bn_or);
      `DEF_MNEM_BIN(mnem_bn_xor);
      illegal_bins other = default;
    }

    // The shifted version of wdr_operand_b is nonzero
    `DEF_SEEN_CP(nz_shifted_cp,
                 0 != (insn_data[30] ?
                       (wdr_operand_b >> {insn_data[29:25], 3'b0}) :
                       (wdr_operand_b << {insn_data[29:25], 3'b0})))

    sb_cp: coverpoint insn_data[29:25] { bins extremes[] = {'0, '1}; }
    st_cp: coverpoint insn_data[30];
    fg_cp: coverpoint insn_data[31];
    // Crossing st_cp, sb_cp and nz_shifted_cp means that we see extremal values of shift in both
    // directions, restricted to cases where the result is nonzero (so the shift actually did
    // something).
    `DEF_MNEM_CROSS3(st, sb, nz_shifted)
    `DEF_MNEM_CROSS(fg)

    `DEF_WDR_TOGGLE_COV(wrs1, wdr_operand_a)
    `DEF_WDR_TOGGLE_COV(wrs2, wdr_operand_b)
    `DEF_WDR_TOGGLE_CROSS(wrs1)
    `DEF_WDR_TOGGLE_CROSS(wrs2)

    // BNA instructions can write the M, L and Z flags, but do not affect the carry flag (bit 0 in
    // the flags_t struct).
    `DEF_MLZ_FLAGS_TOGGLE_COV(flags, flags_write_data[insn_data[31]])
    `DEF_MLZ_FLAGS_TOGGLE_CROSS(flags)

    // Toggle coverage of the output result
    `DEF_WDR_TOGGLE_COV(wrd, wdr_write_data)
    `DEF_WDR_TOGGLE_CROSS(wrd)
  endgroup

  covergroup enc_bnaf_cg
    with function sample(mnem_str_t    mnemonic,
                         logic [31:0]  insn_data,
                         logic [255:0] wdr_operand_a,
                         logic [255:0] wdr_operand_b,
                         flags_t       flags_write_data [2]);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_add);
      `DEF_MNEM_BIN(mnem_bn_addc);
      `DEF_MNEM_BIN(mnem_bn_sub);
      `DEF_MNEM_BIN(mnem_bn_subb);
      illegal_bins other = default;
    }

    // The shifted version of wdr_operand_b is nonzero
    `DEF_SEEN_CP(nz_shifted_cp,
                 0 != (insn_data[30] ?
                       (wdr_operand_b >> {insn_data[29:25], 3'b0}) :
                       (wdr_operand_b << {insn_data[29:25], 3'b0})))

    sb_cp: coverpoint insn_data[29:25] { bins extremes[] = {'0, '1}; }
    st_cp: coverpoint insn_data[30];
    fg_cp: coverpoint insn_data[31];
    // Crossing st_cp, sb_cp and nz_shifted_cp means that we see extremal values of shift in both
    // directions, restricted to cases where the result is nonzero (so the shift actually did
    // something).
    `DEF_MNEM_CROSS3(st, sb, nz_shifted)
    `DEF_MNEM_CROSS(fg)

    `DEF_WDR_TOGGLE_COV(wrs1, wdr_operand_a)
    `DEF_WDR_TOGGLE_COV(wrs2, wdr_operand_b)
    `DEF_WDR_TOGGLE_CROSS(wrs1)
    `DEF_WDR_TOGGLE_CROSS(wrs2)

    `DEF_FLAGS_TOGGLE_COV(flags, flags_write_data[insn_data[31]])
    `DEF_FLAGS_TOGGLE_CROSS(flags)

    // This checks for a nonzero right shift where the top bit of wrs2 is set (ensuring we do a
    // logical shift, not an arithmetic shift).
    `DEF_SEEN_CP(srl_cp,
                 (insn_data[29:25] != 0) && insn_data[30] && wdr_operand_b[255])
    `DEF_MNEM_CROSS(srl)
  endgroup

  covergroup enc_bnai_cg
    with function sample(mnem_str_t    mnemonic,
                         logic [31:0]  insn_data,
                         logic [255:0] wdr_operand_a,
                         flags_t       flags_write_data [2]);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_addi);
      `DEF_MNEM_BIN(mnem_bn_subi);
      illegal_bins other = default;
    }

    imm_cp: coverpoint insn_data[29:20] { bins extremes[] = {'0, '1}; }
    fg_cp: coverpoint insn_data[31];
    `DEF_MNEM_CROSS(imm)
    `DEF_MNEM_CROSS(fg)

    `DEF_WDR_TOGGLE_COV(wrs, wdr_operand_a)
    `DEF_WDR_TOGGLE_CROSS(wrs)

    `DEF_FLAGS_TOGGLE_COV(flags, flags_write_data[insn_data[31]])
    `DEF_FLAGS_TOGGLE_CROSS(flags)
  endgroup

  covergroup enc_bnam_cg
    with function sample(mnem_str_t   mnemonic,
                         logic [31:0] insn_data,
                         logic [255:0] wdr_operand_a,
                         logic [255:0] wdr_operand_b);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_addm);
      `DEF_MNEM_BIN(mnem_bn_subm);
      illegal_bins other = default;
    }

    `DEF_WDR_TOGGLE_COV(wrs1, wdr_operand_a)
    `DEF_WDR_TOGGLE_COV(wrs2, wdr_operand_b)
    `DEF_WDR_TOGGLE_CROSS(wrs1)
    `DEF_WDR_TOGGLE_CROSS(wrs2)
  endgroup

  covergroup enc_bnan_cg
    with function sample(mnem_str_t    mnemonic,
                         logic [31:0]  insn_data,
                         logic [255:0] wdr_operand_a,
                         flags_t       flags_write_data [2],
                         logic [255:0] wdr_write_data);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_not);
      illegal_bins other = default;
    }

    // The shifted version of wdr_operand_a is nonzero
    `DEF_SEEN_CP(nz_shifted_cp,
                 0 != (insn_data[30] ?
                       (wdr_operand_a >> {insn_data[29:25], 3'b0}) :
                       (wdr_operand_a << {insn_data[29:25], 3'b0})))

    sb_cp: coverpoint insn_data[29:25] { bins extremes[] = {'0, '1}; }
    st_cp: coverpoint insn_data[30];
    fg_cp: coverpoint insn_data[31];
    // Crossing st_cp, sb_cp and nz_shifted_cp means that we see extremal values of shift in both
    // directions, restricted to cases where the result is nonzero (so the shift actually did
    // something).
    `DEF_MNEM_CROSS3(st, sb, nz_shifted)

    // Toggle coverage of the input result
    `DEF_WDR_TOGGLE_COV(wrs, wdr_operand_a)

    // BN.NOT can write the M, L and Z flags, but does not affect the carry flag (bit 0 in the
    // flags_t struct).
    `DEF_MLZ_FLAGS_TOGGLE_COV(flags, flags_write_data[insn_data[31]])

    // Toggle coverage of the output result
    `DEF_WDR_TOGGLE_COV(wrd, wdr_write_data)
  endgroup

  covergroup enc_bnaq_cg
    with function sample(mnem_str_t   mnemonic,
                         logic [31:0] insn_data,
                         logic [255:0] wdr_operand_a,
                         logic [255:0] wdr_operand_b);

    // Used for BN.MULQACC
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_mulqacc);
      illegal_bins other = default;
    }

    za_cp: coverpoint insn_data[12];
    shift_cp: coverpoint insn_data[14:13] { bins extremes[] = {'0, '1}; }
    q1_cp: coverpoint insn_data[26:25] { bins extremes[] = {'0, '1}; }
    q2_cp: coverpoint insn_data[28:27] { bins extremes[] = {'0, '1}; }

    qwsel_cross: cross q1_cp, q2_cp;

    `DEF_WDR_TOGGLE_COV(wrs1, wdr_operand_a)
    `DEF_WDR_TOGGLE_COV(wrs2, wdr_operand_b)
  endgroup

  covergroup enc_bnaqs_cg
    with function sample(mnem_str_t   mnemonic,
                         logic [31:0] insn_data,
                         logic [255:0] wdr_operand_a,
                         logic [255:0] wdr_operand_b,
                         flags_t       flags_write_data [2]);

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

    qwsel_cross: cross q1_cp, q2_cp;

    `DEF_WDR_TOGGLE_COV(wrs1, wdr_operand_a)
    `DEF_WDR_TOGGLE_COV(wrs2, wdr_operand_b)

    // BN.MULQACC.SO can write the M, L and Z flags, but does not affect the carry flag (bit 0 in
    // the flags_t struct).
    `DEF_MLZ_FLAGS_TOGGLE_COV(flags, flags_write_data[insn_data[31]])

    // Cross the M, L, Z flag coverpoints above with wrd_hwsel (the "dh" field)
    flags_01_cross: cross dh_cp, flags_01_cp;
    flags_10_cross: cross dh_cp, flags_10_cp;
    flags_11_cross: cross dh_cp, flags_11_cp;
  endgroup

  covergroup enc_bnaqw_cg
    with function sample(mnem_str_t    mnemonic,
                         logic [31:0]  insn_data,
                         logic [255:0] wdr_operand_a,
                         logic [255:0] wdr_operand_b,
                         flags_t       flags_write_data [2]);

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

    qwsel_cross: cross q1_cp, q2_cp;

    `DEF_WDR_TOGGLE_COV(wrs1, wdr_operand_a)
    `DEF_WDR_TOGGLE_COV(wrs2, wdr_operand_b)

    // BN.MULQACC.WO can write the M, L and Z flags, but does not affect the carry flag (bit 0 in
    // the flags_t struct).
    `DEF_MLZ_FLAGS_TOGGLE_COV(flags, flags_write_data[insn_data[31]])
  endgroup

  covergroup enc_bnc_cg
    with function sample(mnem_str_t    mnemonic,
                         logic [31:0]  insn_data,
                         logic [255:0] wdr_operand_a,
                         logic [255:0] wdr_operand_b,
                         flags_t       flags_write_data [2]);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_cmp);
      `DEF_MNEM_BIN(mnem_bn_cmpb);
      illegal_bins other = default;
    }

    // The shifted version of wdr_operand_b is nonzero
    `DEF_SEEN_CP(nz_shifted_cp,
                 0 != (insn_data[30] ?
                       (wdr_operand_b >> {insn_data[29:25], 3'b0}) :
                       (wdr_operand_b << {insn_data[29:25], 3'b0})))

    sb_cp: coverpoint insn_data[29:25] { bins extremes[] = {'0, '1}; }
    st_cp: coverpoint insn_data[30];
    fg_cp: coverpoint insn_data[31];
    // Crossing st_cp, sb_cp and nz_shifted_cp means that we see extremal values of shift in both
    // directions, restricted to cases where the result is nonzero (so the shift actually did
    // something).
    `DEF_MNEM_CROSS3(st, sb, nz_shifted)
    `DEF_MNEM_CROSS(fg)

    `DEF_WDR_TOGGLE_COV(wrs1, wdr_operand_a)
    `DEF_WDR_TOGGLE_COV(wrs2, wdr_operand_b)
    `DEF_WDR_TOGGLE_CROSS(wrs1)
    `DEF_WDR_TOGGLE_CROSS(wrs2)

    `DEF_FLAGS_TOGGLE_COV(flags, flags_write_data[insn_data[31]])
    `DEF_FLAGS_TOGGLE_CROSS(flags)

    // This checks for a nonzero right shift where the top bit of wrs2 is set (ensuring we do a
    // logical shift, not an arithmetic shift).
    `DEF_SEEN_CP(srl_cp,
                 (insn_data[29:25] != 0) && insn_data[30] && wdr_operand_b[255])
    `DEF_MNEM_CROSS(srl)
  endgroup

  covergroup enc_bnmov_cg
    with function sample(mnem_str_t   mnemonic,
                         logic [31:0] insn_data,
                         logic [255:0] wdr_operand_a);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_mov);
      illegal_bins other = default;
    }

    `DEF_WDR_TOGGLE_COV(wrs, wdr_operand_a)
  endgroup

  covergroup enc_bnmovr_cg
    with function sample(mnem_str_t mnemonic,
                         logic [31:0] insn_data,
                         logic [31:0] gpr_operand_a,
                         logic [31:0] gpr_operand_b);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_movr);
      illegal_bins other = default;
    }

    grd_inc_cp: coverpoint insn_data[7];
    grs_inc_cp: coverpoint insn_data[9];
    // See all possible combinations of grd_inc and grs_inc (including the illegal one where both are set)
    inc_cross: cross grd_inc_cp, grs_inc_cp;

    `DEF_GPR_CP(grs_cp, 19:15)
    `DEF_GPR_CP(grd_cp, 24:20)
    `DEF_MNEM_CROSS2(grs, grd)

    `DEF_GPR_TOGGLE_COV(grs, gpr_operand_a)
    `DEF_GPR_TOGGLE_COV(grd, gpr_operand_b)

    big_grd_cp: coverpoint (gpr_operand_a >= 32);
    big_grs_cp: coverpoint (gpr_operand_b >= 32);
    big_gpr_cross: cross big_grd_cp, big_grs_cp;
  endgroup

  covergroup enc_bnr_cg
    with function sample(mnem_str_t   mnemonic,
                         logic [31:0] insn_data,
                         logic [255:0] wdr_operand_a,
                         logic [255:0] wdr_operand_b);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_rshi);
      illegal_bins other = default;
    }

    imm_cp: coverpoint {insn_data[31:25], insn_data[14]} { bins extremes[] = {'0, '1}; }

    `DEF_WDR_TOGGLE_COV(wrs1, wdr_operand_a)
    `DEF_WDR_TOGGLE_COV(wrs2, wdr_operand_b)
  endgroup

  covergroup enc_bns_cg
    with function sample(mnem_str_t   mnemonic,
                         logic [31:0] insn_data,
                         logic [255:0] wdr_operand_a,
                         logic [255:0] wdr_operand_b,
                         flags_t      flags_read_data[2]);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_sel);
      illegal_bins other = default;
    }

    // Note: We cover each of the 4 flags here, not just the extremes
    flag_cp: coverpoint insn_data[26:25];
    fg_cp: coverpoint insn_data[31];

    `DEF_WDR_TOGGLE_COV(wrs1, wdr_operand_a)
    `DEF_WDR_TOGGLE_COV(wrs2, wdr_operand_b)

    flag_value_cp: coverpoint flags_read_data[insn_data[31]][insn_data[26:25]];
    flag_cross: cross fg_cp, flag_cp, flag_value_cp;
  endgroup

  covergroup enc_bnxid_cg
    with function sample(mnem_str_t mnemonic,
                         logic [31:0] insn_data,
                         logic [31:0] gpr_operand_a,
                         logic [31:0] gpr_operand_b);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_lid);
      `DEF_MNEM_BIN(mnem_bn_sid);
      illegal_bins other = default;
    }

    incd_cp: coverpoint insn_data[7];
    inc1_cp: coverpoint insn_data[8];
    off_cp: coverpoint {insn_data[31:25], insn_data[11:9]} { bins extremes[] = {'0, '1}; }
    // See all possible combinations of incd and inc1 (including the illegal one where both are set)
    `DEF_MNEM_CROSS2(incd, inc1)
    `DEF_MNEM_CROSS(off)

    `DEF_GPR_CP(grs1_cp, 19:15)
    // Note: Bits 24:20 are called grd for BN.LID or grs2 for BN.SID, but both are a GPR, so can be
    //       tracked the same here.
    `DEF_GPR_CP(grx_cp, 24:20)
    `DEF_MNEM_CROSS2(grs1, grx)

    `DEF_GPR_TOGGLE_COV(grs1, gpr_operand_a)
    `DEF_GPR_TOGGLE_COV(grs2, gpr_operand_b)
    `DEF_GPR_TOGGLE_CROSS(grs1)
    `DEF_GPR_TOGGLE_CROSS(grs2)

    // Cross the three types of GPR for GRS1 with grs1_inc
    `DEF_MNEM_CROSS2(grs1, inc1)
    // Cross the three types of GPR for GRD/GRS2 with grd_inc/grs2_inc
    `DEF_MNEM_CROSS2(grx, incd)
  endgroup

  covergroup enc_b_cg
    with function sample(mnem_str_t mnemonic,
                         logic [31:0] insn_data,
                         logic [31:0] gpr_operand_a,
                         logic [31:0] gpr_operand_b);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_beq);
      `DEF_MNEM_BIN(mnem_bne);
      illegal_bins other = default;
    }

    off_cp: coverpoint {insn_data[31], insn_data[7], insn_data[30:25], insn_data[11:8]} {
      bins extremes[] = {12'h800, 12'h7ff};
    }
    `DEF_MNEM_CROSS(off)

    `DEF_GPR_CP(grs1_cp, 19:15)
    `DEF_GPR_CP(grs2_cp, 24:20)
    `DEF_MNEM_CROSS2(grs1, grs2)

    `DEF_GPR_TOGGLE_COV(grs1, gpr_operand_a)
    `DEF_GPR_TOGGLE_COV(grs2, gpr_operand_b)
    `DEF_GPR_TOGGLE_CROSS(grs1)
    `DEF_GPR_TOGGLE_CROSS(grs2)
  endgroup

  covergroup enc_ecall_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    // Used by the ECALL instruction. Although it uses the I encoding in the tooling, it has no
    // immediate or register operands so we give it a separate covergroup here.
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_ecall);
      illegal_bins other = default;
    }
  endgroup

  covergroup enc_i_cg
    with function sample(mnem_str_t mnemonic,
                         logic [31:0] insn_data,
                         logic [31:0] gpr_operand_a);

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
    `DEF_MNEM_CROSS(imm)

    `DEF_GPR_CP(grd_cp, 11:7)
    `DEF_GPR_CP(grs1_cp, 19:15)
    `DEF_MNEM_CROSS2(grd, grs1)

    `DEF_GPR_TOGGLE_COV(grs1, gpr_operand_a)
    `DEF_GPR_TOGGLE_CROSS(grs1)
  endgroup

  covergroup enc_is_cg
    with function sample(mnem_str_t mnemonic,
                         logic [31:0] insn_data,
                         logic [31:0] gpr_operand_a);

    // Instructions with the Is encoding
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_slli);
      `DEF_MNEM_BIN(mnem_srli);
      `DEF_MNEM_BIN(mnem_srai);
      illegal_bins other = default;
    }

    shamt_cp: coverpoint insn_data[24:20] { bins extremes[] = {'0, '1}; }
    `DEF_MNEM_CROSS(shamt)

    `DEF_GPR_CP(grd_cp, 11:7)
    `DEF_GPR_CP(grs1_cp, 19:15)
    `DEF_MNEM_CROSS2(grd, grs1)

    `DEF_GPR_TOGGLE_COV(grs1, gpr_operand_a)
    `DEF_GPR_TOGGLE_CROSS(grs1)
  endgroup

  covergroup enc_j_cg with function sample(mnem_str_t mnemonic, logic [31:0] insn_data);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_jal);
      illegal_bins other = default;
    }

    off_cp: coverpoint insn_data[31:12] { bins extremes[] = {20'h80000, 20'h7ffff}; }

    `DEF_GPR_CP(grd_cp, 11:7)
  endgroup

  covergroup enc_loop_cg
    with function sample(mnem_str_t mnemonic,
                         logic [31:0] insn_data,
                         logic [31:0] gpr_operand_a);

    // Used for LOOP encoding (just the LOOP instruction)
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_loop);
      illegal_bins other = default;
    }

    sz_cp: coverpoint insn_data[31:20] { bins extremes[] = {'0, '1}; }

    `DEF_GPR_CP(grs_cp, 19:15)

    `DEF_GPR_TOGGLE_COV(grs, gpr_operand_a)
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

  covergroup enc_r_cg
    with function sample(mnem_str_t mnemonic,
                         logic [31:0] insn_data,
                         logic [31:0] gpr_operand_a,
                         logic [31:0] gpr_operand_b);

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

    `DEF_GPR_TOGGLE_COV(grs1, gpr_operand_a)
    `DEF_GPR_TOGGLE_COV(grs2, gpr_operand_b)
    `DEF_GPR_TOGGLE_CROSS(grs1)
    `DEF_GPR_TOGGLE_CROSS(grs2)
  endgroup

  covergroup enc_s_cg
    with function sample(mnem_str_t mnemonic,
                         logic [31:0] insn_data,
                         logic [31:0] gpr_operand_a,
                         logic [31:0] gpr_operand_b);

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

    `DEF_GPR_TOGGLE_COV(grs1, gpr_operand_a)
    `DEF_GPR_TOGGLE_COV(grs2, gpr_operand_b)
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

    wsr_imm_cp: coverpoint insn_data[27:20] { bins extremes[] = {'0, '1}; }
    `DEF_MNEM_CROSS(wsr_imm)

    `DEF_WSR_CP(wsr_cp, insn_data[27:20])
    `DEF_MNEM_CROSS(wsr)
  endgroup

  // Per-instruction covergroups ///////////////////////////////////////////////

  covergroup insn_addsub_cg
    with function sample(mnem_str_t   mnemonic,
                         logic [31:0] operand_a,
                         logic [31:0] operand_b);
    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_add);
      `DEF_MNEM_BIN(mnem_sub);
      illegal_bins other = default;
    }

    `DEF_SIGN_CP(sign_a_cp, operand_a, 32)
    `DEF_SIGN_CP(sign_b_cp, operand_b, 32)
    `DEF_MNEM_CROSS2(sign_a, sign_b)
  endgroup

  covergroup insn_addi_cg
    with function sample(logic [31:0] insn_data,
                         logic [31:0] operand_a);
    `DEF_SIGN_CP(sign_a_cp, operand_a, 32)
    `DEF_SIGN_CP(sign_b_cp, insn_data[31:20], 12)
    sign_cross: cross sign_a_cp, sign_b_cp;
  endgroup

  covergroup insn_sll_cg
    with function sample(logic [31:0] operand_a,
                         logic [31:0] operand_b);

    // A shift of a nonzero value by zero
    `DEF_SEEN_CP(nz_by_z_cp, (operand_a != 0) && (operand_b == 0))
    // A shift of a value by 0x1f, leaving the top bit set (because the bottom bit of the value was
    // nonzero)
    `DEF_SEEN_CP(shift15_cp, operand_a[0] && ((operand_b & 'h1f) == 'h1f))
  endgroup

  covergroup insn_slli_cg
    with function sample(logic [31:0] insn_data,
                         logic [31:0] operand_a);

    // A shift of a nonzero value by zero
    `DEF_SEEN_CP(nz_by_z_cp, (operand_a != 0) && (insn_data[24:20] == 0))
    // A shift of a value by 0x1f, leaving the top bit set (because the bottom bit of the value was
    // nonzero)
    `DEF_SEEN_CP(shift15_cp, operand_a[0] && (insn_data[24:20] == 5'h1f))
  endgroup

  covergroup insn_srl_cg
    with function sample(logic [31:0] operand_a,
                         logic [31:0] operand_b);

    // A shift of a nonzero value by zero
    `DEF_SEEN_CP(nz_by_z_cp, (operand_a != 0) && (operand_b == 0))
    // A shift of a value by 0x1f, leaving the bottom bit set (because the top bit of the value was
    // nonzero)
    `DEF_SEEN_CP(shift15_cp, operand_a[31] && ((operand_b & 'h1f) == 'h1f))
  endgroup

  covergroup insn_srli_cg
    with function sample(logic [31:0] insn_data,
                         logic [31:0] operand_a);

    // A shift of a nonzero value by zero
    `DEF_SEEN_CP(nz_by_z_cp, (operand_a != 0) && (insn_data[24:20] == 0))
    // A shift of a value by 0x1f, leaving the bottom bit set (because the top bit of the value was
    // nonzero)
    `DEF_SEEN_CP(shift15_cp, operand_a[31] && (insn_data[24:20] == 5'h1f))
  endgroup

  covergroup insn_sra_cg
    with function sample(logic [31:0] operand_a,
                         logic [31:0] operand_b);

    // A shift of a nonzero value by zero
    `DEF_SEEN_CP(nz_by_z_cp, (operand_a != 0) && (operand_b == 0))
    // A shift of a value by 0x1f, leaving the bottom bit set (because the top bit of the value was
    // nonzero)
    `DEF_SEEN_CP(shift15_cp, operand_a[31] && ((operand_b & 'h1f) == 'h1f))
  endgroup

  covergroup insn_srai_cg
    with function sample(logic [31:0] insn_data,
                         logic [31:0] operand_a);

    // A shift of a nonzero value by zero
    `DEF_SEEN_CP(nz_by_z_cp, (operand_a != 0) && (insn_data[24:20] == 0))
    // A shift of a value by 0x1f, leaving the bottom bit set (because the top bit of the value was
    // nonzero)
    `DEF_SEEN_CP(shift15_cp, operand_a[31] && (insn_data[24:20] == 5'h1f))
  endgroup

  // A covergroup used for logical binary operations.
  //
  // For each of these operations, we want to see "toggle coverage" of the output result and expect
  // that the output register is not x0. To handle this easily, we only call sample() when the
  // output register is nonzero (checked with x0_cp).
  covergroup insn_log_binop_cg
    with function sample(mnem_str_t   mnemonic,
                         logic [31:0] insn_data,
                         logic [31:0] gpr_write_data);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_and);
      `DEF_MNEM_BIN(mnem_andi);
      `DEF_MNEM_BIN(mnem_or);
      `DEF_MNEM_BIN(mnem_ori);
      `DEF_MNEM_BIN(mnem_xor);
      `DEF_MNEM_BIN(mnem_xori);
      illegal_bins other = default;
    }

    // Check we don't call sample when GRD is 0.
    x0_cp: coverpoint insn_data[11:7] { illegal_bins x0 = {0}; }

    `DEF_GPR_TOGGLE_COV(write_data, gpr_write_data)
    `DEF_GPR_TOGGLE_CROSS(write_data)
  endgroup

  // A covergroup used for LW and SW. The "offset" argument to sample is the immediate offset from
  // the instruction encoding. We extract that in the giant case statement in on_insn() so that we
  // reuse the code for LW and SW (which encode the fields differently).
  covergroup insn_xw_cg
    with function sample(mnem_str_t          mnemonic,
                         logic [11:0]        offset,
                         logic [4:0]         grs1,
                         logic [4:0]         grx2,
                         logic [31:0]        operand_a,
                         logic signed [31:0] addr,
                         stack_fullness_e    call_stack_fullness,
                         logic               call_stack_underflow);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_lw);
      `DEF_MNEM_BIN(mnem_sw);
      illegal_bins other = default;
    }

    // Load from a valid address, where grs1 is above the top of memory and a negative offset brings
    // the load address in range.
    `DEF_SEEN_CP(oob_base_neg_off_cp,
                 ($signed(operand_a) > DmemSizeByte) &&
                 ($signed(offset) < 0) &&
                 (0 <= addr) && (addr + 4 <= DmemSizeByte) && ((addr & 32'h3) == 0))
    `DEF_MNEM_CROSS(oob_base_neg_off)

    // Load from a valid address, where grs1 is negative and a positive offset brings the load
    // address in range.
    `DEF_SEEN_CP(neg_base_pos_off_cp,
                 ($signed(operand_a) < 0) && ($signed(offset) > 0) &&
                 (0 <= addr) && (addr + 4 <= DmemSizeByte) && ((addr & 32'h3) == 0))
    `DEF_MNEM_CROSS(neg_base_pos_off)

    // Load from address zero
    `DEF_SEEN_CP(addr0_cp, addr == 0)
    `DEF_MNEM_CROSS(addr0)

    // Load from the top word of memory
    `DEF_SEEN_CP(top_addr_cp, addr == DmemSizeByte - 4)
    `DEF_MNEM_CROSS(top_addr)

    // Load from an invalid address (aligned but above the top of memory)
    `DEF_SEEN_CP(oob_addr_cp, (addr > DmemSizeByte - 4) && ((addr & 32'h3) == 0))
    `DEF_MNEM_CROSS(oob_addr)

    // Load from a negative invalid address (aligned but unsigned address exceeds the top of memory)
    `DEF_SEEN_CP(oob_addr_neg_cp, (addr < 0) && ((addr & 32'h3) == 0))
    `DEF_MNEM_CROSS(oob_addr_neg)

    // Load from a "barely invalid" address (the smallest aligned address that's above the top of
    // memory)
    `DEF_SEEN_CP(barely_oob_addr_cp, addr == DmemSizeByte)
    `DEF_MNEM_CROSS(barely_oob_addr)

    // Cross the different possible address alignments for otherwise valid addresses
    grs1_align_cp: coverpoint operand_a[1:0];
    offset_align_cp: coverpoint offset[1:0];
    align_cross:
      cross mnemonic_cp, grs1_align_cp, offset_align_cp
        iff ((0 <= addr) && (addr + 4 <= DmemSizeByte));

    // Overflow the call stack when accessing an invalid address. Note that this is only possible
    // for LW (since SW never pushes to the call stack). Also note that we have to compute whether
    // this is an overflow: we'll never see the push to a full call stack on the initial cycle of
    // the instruction because the load data comes back on the following cycle.
    `DEF_SEEN_CP(overflow_cs_invalid_addr_cp,
                 (call_stack_fullness == StackFull) && (grx2 == 1) &&
                 (addr < 0 || (addr + 4 > DmemSizeByte) || (addr & 32'h3) != 0))

    // Underflow the call stack when accessing an invalid address. We have to be a bit careful here
    // to make sure this is an SW instruction and we're underflowing with grs2 rather than grs1.
    `DEF_SEEN_CP(underflow_cs_invalid_addr_cp,
                 mnemonic == mnem_sw &&
                 call_stack_underflow &&
                 grs1 != 5'd1 &&
                 (addr < 0 || (addr + 4 > DmemSizeByte) || (addr & 32'h3) != 0))
  endgroup

  covergroup insn_bxx_cg
    with function sample(mnem_str_t          mnemonic,
                         logic [31:0]        insn_addr,
                         logic [12:0]        offset,
                         logic [31:0]        operand_a,
                         logic [31:0]        operand_b,
                         logic signed [31:0] tgt_addr,
                         logic               at_current_loop_end_insn,
                         logic               call_stack_underflow);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_beq);
      `DEF_MNEM_BIN(mnem_bne);
      illegal_bins other = default;
    }

    eq_cp: coverpoint operand_a == operand_b;

    `DEF_SIGN_CP(dir_cp, offset, 13)
    `DEF_MNEM_CROSS2(eq, dir)

    offset_align_cp: coverpoint offset[1];
    `DEF_MNEM_CROSS2(eq, offset_align)

    `DEF_SEEN_CP(oob_cp, tgt_addr > ImemSizeByte)
    `DEF_MNEM_CROSS2(eq, oob)

    `DEF_SEEN_CP(neg_cp, tgt_addr < 0)
    `DEF_MNEM_CROSS2(eq, neg)

    at_loop_end_cp: coverpoint at_current_loop_end_insn;
    `DEF_MNEM_CROSS2(eq, at_loop_end)

    // A branch at the end of a loop where we also underflow the call stack
    `DEF_SEEN_CP(underflow_at_loop_end_cp, at_current_loop_end_insn && call_stack_underflow)
    `DEF_MNEM_CROSS(underflow_at_loop_end)

    // A branch at the end of a loop that is taken and points at a bad address
    `DEF_SEEN_CP(bad_addr_at_loop_end_cp,
                 at_current_loop_end_insn &&
                 ((mnemonic == mnem_beq) ? (operand_a == operand_b) : (operand_a != operand_b)) &&
                 (tgt_addr < 0 || tgt_addr > ImemSizeByte || tgt_addr[1:0] != 0))
    `DEF_MNEM_CROSS(bad_addr_at_loop_end)
  endgroup

  covergroup insn_jal_cg
    with function sample(logic [31:0]        insn_addr,
                         logic [20:0]        offset,
                         logic signed [31:0] tgt_addr,
                         logic               at_current_loop_end_insn,
                         logic               call_stack_overflow);

    `DEF_SIGN_CP(dir_cp, offset, 21)
    offset_align_cp: coverpoint offset[1:0] {
      bins allowed[] = {0, 2};
      illegal_bins other = default;
    }

    `DEF_SEEN_CP(oob_cp, tgt_addr > ImemSizeByte)
    `DEF_SEEN_CP(neg_cp, tgt_addr < 0)
    `DEF_SEEN_CP(from_top_cp, insn_addr == ImemSizeByte - 4)

    at_loop_end_cp: coverpoint at_current_loop_end_insn;

    // Overflow the call stack when jumping to an invalid address
    `DEF_SEEN_CP(overflow_and_invalid_addr_cp,
                 call_stack_overflow &&
                 (tgt_addr < 0 || tgt_addr > ImemSizeByte || tgt_addr[1:0] != 0))

    // Overflow the call stack at the end of a loop
    `DEF_SEEN_CP(overflow_at_loop_end_cp,
                 call_stack_overflow && at_current_loop_end_insn)

    // Jump to an invalid address at the end of a loop
    `DEF_SEEN_CP(invalid_addr_at_loop_end_cp,
                 (tgt_addr < 0 || tgt_addr > ImemSizeByte || tgt_addr[1:0] != 0) &&
                 at_current_loop_end_insn)

    // Overflow the call stack while jumping to an invalid address at the end of a loop
    `DEF_SEEN_CP(overflow_and_invalid_addr_at_loop_end_cp,
                 call_stack_overflow &&
                 (tgt_addr < 0 || tgt_addr > ImemSizeByte || tgt_addr[1:0] != 0) &&
                 at_current_loop_end_insn)
  endgroup

  covergroup insn_jalr_cg
    with function sample(logic [31:0]        insn_addr,
                         logic [11:0]        offset,
                         logic signed [31:0] tgt_addr,
                         logic [31:0]        operand_a,
                         logic               at_current_loop_end_insn,
                         logic               call_stack_underflow,
                         logic               call_stack_overflow);

    `DEF_SIGN_CP(off_dir_cp, offset, 12)

    offset_align_cp: coverpoint offset[1:0];
    base_align_cp: coverpoint operand_a[1:0];
    align_cross: cross offset_align_cp, base_align_cp;

    // Jump with a large base address which wraps to a valid address by adding a positive offset.
    `DEF_SEEN_CP(pos_wrap_cp,
                 (operand_a >= ImemSizeByte) &&
                 ($signed(offset) > 0) &&
                 (tgt_addr <= ImemSizeByte - 4))

    // Jump with a base address just above top of IMEM but with a negative offset to give a valid
    // target.
    `DEF_SEEN_CP(sub_cp,
                 (operand_a >= ImemSizeByte) &&
                 ($signed(offset) < 0) &&
                 (tgt_addr <= ImemSizeByte - 4))

    // Jump with a negative offset, wrapping to give an invalid target.
    `DEF_SEEN_CP(neg_wrap_cp,
                 (operand_a <= ImemSizeByte - 4) &&
                 ($signed(offset) < 0) &&
                 (tgt_addr > ImemSizeByte - 4))

    // Jump to an aligned address above top of IMEM.
    `DEF_SEEN_CP(oob_cp, (((tgt_addr) & 32'h3) == 0) && (tgt_addr > ImemSizeByte - 4))

    // Jump to current address.
    `DEF_SEEN_CP(self_cp, tgt_addr == insn_addr)

    // Jump when the current PC is the top word in IMEM.
    `DEF_SEEN_CP(from_top_cp, insn_addr == ImemSizeByte - 4)

    // Is this jump the last instruction of the current loop?
    at_loop_end_cp: coverpoint at_current_loop_end_insn;

    // Underflow call stack at end of loop
    `DEF_SEEN_CP(underflow_at_loop_end_cp, call_stack_underflow && at_current_loop_end_insn)

    // Overflow call stack when jumping to an invalid address
    `DEF_SEEN_CP(overflow_and_bad_addr_cp,
                 call_stack_overflow &&
                 (tgt_addr < 0 || tgt_addr >= ImemSizeByte || tgt_addr[1:0] != 0))

    // Overflow call stack at end of loop
    `DEF_SEEN_CP(overflow_at_loop_end_cp, call_stack_overflow && at_current_loop_end_insn)

    // Jump to an invalid address at the end of a loop
    `DEF_SEEN_CP(bad_addr_at_loop_end_cp,
                 (tgt_addr < 0 || tgt_addr >= ImemSizeByte || tgt_addr[1:0] != 0) &&
                 at_current_loop_end_insn)

    // Overflow call stack when jumping to an invalid address at the end of a loop
    `DEF_SEEN_CP(overflow_and_bad_addr_at_loop_end_cp,
                 call_stack_overflow &&
                 (tgt_addr < 0 || tgt_addr >= ImemSizeByte || tgt_addr[1:0] != 0) &&
                 at_current_loop_end_insn)
  endgroup

  covergroup insn_csrrs_cg
    with function sample(logic [31:0]     insn_data,
                         logic [31:0]     operand_a,
                         stack_fullness_e call_stack_fullness);

    `DEF_CSR_CP(csr_cp, insn_data[31:20])
    `DEF_NZ_CP(bits_to_set_cp, operand_a)

    csr_cross: cross csr_cp, bits_to_set_cp;

    // Underflow the call stack while accessing an invalid CSR. The RTL squashes the GPR reads in
    // this case, so we have to figure out a call stack underflow by hand (true if the call stack
    // was empty and grs1 is x1)
    `DEF_SEEN_CP(underflow_with_bad_csr_cp,
                 (call_stack_fullness == StackEmpty) && (insn_data[19:15] == 5'd1) &&
                 (remap_csr(insn_data[31:20]) == -1))

    // Overflow the call stack while accessing an invalid CSR. The RTL squashes the GPR reads in
    // this case, so we have to figure out a call stack underflow by hand (true if the call stack
    // was full and grd is x1)
    `DEF_SEEN_CP(overflow_with_bad_csr_cp,
                 (call_stack_fullness == StackFull) && (insn_data[11:7] == 5'd1) &&
                 (remap_csr(insn_data[31:20]) == -1))
  endgroup

  covergroup insn_csrrw_cg
    with function sample(logic [31:0] insn_data,
                         stack_fullness_e call_stack_fullness);

    `DEF_CSR_CP(csr_cp, insn_data[31:20])
    `DEF_NZ_CP(grd_cp, insn_data[11:7])

    csr_cross: cross csr_cp, grd_cp;

    `DEF_SEEN_CP(uimp_cp, insn_data == 32'hC0001073)

    // Underflow the call stack while accessing an invalid CSR. The RTL squashes the GPR reads in
    // this case, so we have to figure out a call stack underflow by hand (true if the call stack
    // was empty and grs1 is x1)
    `DEF_SEEN_CP(underflow_with_bad_csr_cp,
                 (call_stack_fullness == StackEmpty) && (insn_data[19:15] == 5'd1) &&
                 (remap_csr(insn_data[31:20]) == -1))

    // Overflow the call stack while accessing an invalid CSR. The RTL squashes the GPR reads in
    // this case, so we have to figure out a call stack underflow by hand (true if the call stack
    // was full and grd is x1)
    `DEF_SEEN_CP(overflow_with_bad_csr_cp,
                 (call_stack_fullness == StackFull) && (insn_data[11:7] == 5'd1) &&
                 (remap_csr(insn_data[31:20]) == -1))
  endgroup

  covergroup insn_loop_cg
    with function sample(logic [31:0]     insn_addr,
                         logic [31:0]     insn_data,
                         logic [31:0]     operand_a,
                         stack_fullness_e loop_stack_fullness,
                         logic [31:0]     current_loop_end,
                         logic [31:0]     bodysize,
                         logic            at_loop_end,
                         logic            call_stack_underflow);
    // Extremes for iteration count
    iterations_cp: coverpoint operand_a { bins extremes[] = {'0, '1}; }

    // Is the loop end address above the top of memory?
    oob_end_addr_cp: coverpoint insn_addr + 4 * bodysize >= ImemSizeByte;

    // Current state of the loop stack (empty, half full, full)
    loop_stack_fullness_cp: coverpoint loop_stack_fullness;

    // Is this loop the last instruction of the current loop?
    at_loop_end_cp: coverpoint at_loop_end;

    // Does the loop end for this instruction match the top of a nonempty loop stack? If valid,
    // current_loop_end is the address of the last instruction in the loop body. The last
    // instruction of the current loop body is the current PC plus 4 for the LOOP instruction and
    // then 4 * (bodysize - 1) for all but the last instruction of the loop body.
    `DEF_SEEN_CP(duplicate_loop_end_cp,
                 (loop_stack_fullness != StackEmpty) &&
                 (current_loop_end == insn_addr + 4 * bodysize))

    // Underflow the call stack at the end of a loop
    `DEF_SEEN_CP(underflow_at_loop_end_cp, at_loop_end && call_stack_underflow)

    // A zero loop count at the end of a loop
    `DEF_SEEN_CP(zero_count_at_loop_end_cp, at_loop_end && (operand_a == 0))
  endgroup

  covergroup insn_loopi_cg
    with function sample(logic [31:0]     insn_addr,
                         logic [31:0]     insn_data,
                         stack_fullness_e loop_stack_fullness,
                         logic [31:0]     current_loop_end,
                         logic [9:0]      iterations,
                         logic [31:0]     bodysize,
                         logic            at_loop_end);

    // Is the loop end address above the top of memory?
    oob_end_addr_cp: coverpoint insn_addr + 4 * bodysize >= ImemSizeByte;

    // Current state of the loop stack (empty, half full, full)
    loop_stack_fullness_cp: coverpoint loop_stack_fullness;

    // Is this loop the last instruction of the current loop?
    at_loop_end_cp: coverpoint at_loop_end;

    // Does the loop end for this instruction match the top of a nonempty loop stack? If valid,
    // current_loop_end is the address of the last instruction in the loop body. The last
    // instruction of the current loop body is the current PC plus 4 for the LOOPI instruction and
    // then 4 * (bodysize - 1) for all but the last instruction of the loop body.
    `DEF_SEEN_CP(duplicate_loop_end_cp,
                 (loop_stack_fullness != StackEmpty) &&
                 (current_loop_end == insn_addr + 4 * bodysize))

    // A zero loop count at the end of a loop
    `DEF_SEEN_CP(zero_count_at_loop_end_cp, at_loop_end && (iterations == 0))
  endgroup

  covergroup insn_bn_addc_cg
    with function sample(logic [31:0] insn_data,
                         flags_t      flags_read_data[2]);

    // Execute with both values of the carry flag for both flag groups
    fg_cp: coverpoint insn_data[31];
    carry_flag_cp: coverpoint flags_read_data[insn_data[31]].C;
    carry_cross: cross fg_cp, carry_flag_cp;

  endgroup

  covergroup insn_bn_addm_cg
    with function sample(logic [31:0]  insn_data,
                         logic [255:0] wdr_operand_a,
                         logic [255:0] wdr_operand_b,
                         logic [255:0] mod);

    // Extreme values of MOD
    mod_cp: coverpoint mod { bins extremes[] = {'0, '1}; }

    // Sum less than MOD (so we don't do a subtraction). Here, and below, we zero-extend explicitly
    // in the sum, which uses 257 bits internally.
    `DEF_SEEN_CP(sum_lt_cp,
                 (mod != 0) && ({1'b0, wdr_operand_a} + {1'b0, wdr_operand_b} < {1'b0, mod}))

    // Sum exactly equals a nonzero MOD (subtracting down to zero)
    `DEF_SEEN_CP(sum_eq_cp,
                 (mod != 0) && ({1'b0, wdr_operand_a} + {1'b0, wdr_operand_b} == {1'b0, mod}))

    // Sum is greater than a nonzero MOD, but not twice as big.
    `DEF_SEEN_CP(sum_gt_cp,
                 (mod != 0) &&
                 ({1'b0, wdr_operand_a} + {1'b0, wdr_operand_b} > {1'b0, mod}) &&
                 ({1'b0, wdr_operand_a} + {1'b0, wdr_operand_b} < {mod, 1'b0}))

    // Sum is at least twice a nonzero MOD.
    `DEF_SEEN_CP(sum_gt2_cp,
                 (mod != 0) &&
                 ({1'b0, wdr_operand_a} + {1'b0, wdr_operand_b} >= {mod, 1'b0}))

    // The intermediate sum overflows 256 bits
    `DEF_SEEN_CP(overflow_cp,
                 (({1'b0, wdr_operand_a} + {1'b0, wdr_operand_b}) >> 256) != 0)

    // Wrap after subtraction?
    wrap_after_mod_cp: coverpoint ((({1'b0, wdr_operand_a} + {1'b0, wdr_operand_b} > {1'b0, mod}) ?
                                    ({1'b0, wdr_operand_a} + {1'b0, wdr_operand_b} - {1'b0, mod}) :
                                    ({1'b0, wdr_operand_a} + {1'b0, wdr_operand_b})) >> 256) != 0;

    overflow_wrap_cross: cross overflow_cp, wrap_after_mod_cp;
  endgroup

  covergroup insn_bn_mulqaccx_cg
    with function sample(mnem_str_t   mnemonic,
                         logic [256:0] new_acc_extended);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_mulqacc);
      `DEF_MNEM_BIN(mnem_bn_mulqacc_so);
      `DEF_MNEM_BIN(mnem_bn_mulqacc_wo);
      illegal_bins other = default;
    }

    // ACC will be truncated (the sum overflowed)
    `DEF_SEEN_CP(overflow_cp, new_acc_extended[256])
    `DEF_MNEM_CROSS(overflow)

  endgroup

  covergroup insn_bn_subcmpb_cg
    with function sample(mnem_str_t   mnemonic,
                         logic [31:0] insn_data,
                         flags_t      flags_read_data[2]);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_subb);
      `DEF_MNEM_BIN(mnem_bn_cmpb);
      illegal_bins other = default;
    }

    // Execute with both values of the carry flag (borrow here!) for both flag groups
    fg_cp: coverpoint insn_data[31];
    carry_flag_cp: coverpoint flags_read_data[insn_data[31]].C;
    `DEF_MNEM_CROSS2(fg, carry_flag)

  endgroup

  covergroup insn_bn_subm_cg
    with function sample(logic [31:0]  insn_data,
                         logic [255:0] wdr_operand_a,
                         logic [255:0] wdr_operand_b,
                         logic [255:0] mod);

    // Extreme values of MOD
    mod_cp: coverpoint mod { bins extremes[] = {'0, '1}; }

    // A non-negative difference with a nonzero MOD.
    `DEF_SEEN_CP(diff_nonneg_cp,
                 (mod != 0) && ({1'b0, wdr_operand_a} - {1'b0, wdr_operand_b} < {1'b1, 256'b0}))

    // Difference exactly equals a nonzero -MOD (adding back up to zero)
    `DEF_SEEN_CP(diff_minus_mod_cp,
                 (mod != 0) &&
                 ({1'b0, wdr_operand_a} - {1'b0, wdr_operand_b} + {1'b0, mod} == 0))

    // Difference is between -MOD and -1.
    `DEF_SEEN_CP(diff_neg_cp,
                 (mod != 0) &&
                 ({1'b0, wdr_operand_a} - {1'b0, wdr_operand_b} >= {1'b1, 256'b0}) &&
                 ({1'b0, wdr_operand_a} - {1'b0, wdr_operand_b} + {1'b0, mod} < {1'b1, 256'b0}))

    // Difference is less than -MOD
    `DEF_SEEN_CP(diff_neg2_cp,
                 (mod != 0) &&
                 (mod != 0) &&
                 ({1'b0, wdr_operand_a} - {1'b0, wdr_operand_b} >= {1'b1, 256'b0}) &&
                 ({1'b0, wdr_operand_a} - {1'b0, wdr_operand_b} + {1'b0, mod} >= {1'b1, 256'b0}))
  endgroup

  // Used by BN.LID and BN.SID
  covergroup insn_bn_xid_cg
    with function sample(mnem_str_t          mnemonic,
                         logic [14:0]        offset,
                         logic [31:0]        operand_a,
                         logic [31:0]        operand_b,
                         logic signed [31:0] addr,
                         logic               inc_both,
                         logic [4:0]         grs1,
                         logic [4:0]         grx2,
                         logic               call_stack_underflow);

    mnemonic_cp: coverpoint mnemonic {
      `DEF_MNEM_BIN(mnem_bn_lid);
      `DEF_MNEM_BIN(mnem_bn_sid);
      illegal_bins other = default;
    }

    // Access a valid address, where grs1 is above the top of memory and a negative offset brings
    // the address in range.
    `DEF_SEEN_CP(oob_base_neg_off_cp,
                 ($signed(operand_a) > DmemSizeByte) &&
                 ($signed(offset) < 0) &&
                 (0 <= addr) && (addr + 32 <= DmemSizeByte) && ((addr & 32'd31) == 0))
    `DEF_MNEM_CROSS(oob_base_neg_off)

    // Access a valid address, where grs1 is negative and a positive offset brings the address in
    // range.
    `DEF_SEEN_CP(neg_base_pos_off_cp,
                 ($signed(operand_a) < 0) &&
                 ($signed(offset) > 0) &&
                 (0 <= addr) && (addr + 32 <= DmemSizeByte) && ((addr & 32'd31) == 0))
    `DEF_MNEM_CROSS(neg_base_pos_off)

    // Access address zero
    `DEF_SEEN_CP(addr0_cp, addr == 0)
    `DEF_MNEM_CROSS(addr0)

    // Access the top word of memory
    `DEF_SEEN_CP(top_addr_cp, addr == DmemSizeByte - 32)
    `DEF_MNEM_CROSS(top_addr)

    // Access an invalid address (aligned but above the top of memory)
    `DEF_SEEN_CP(oob_addr_cp,
                 (addr > DmemSizeByte - 32) && ((addr & 32'd31) == 0))
    `DEF_MNEM_CROSS(oob_addr)

    // Load from a negative invalid address (aligned but unsigned address exceeds the top of memory)
    `DEF_SEEN_CP(oob_addr_neg_cp,
                 (addr < 0) && ((addr & 32'h3) == 0))
    `DEF_MNEM_CROSS(oob_addr_neg)

    // Misaligned address tracking (see DV document for why we have these exact crosses)
    addr_align_cp: coverpoint operand_a[4:0];

    addr_align_cross:
      cross mnemonic_cp, addr_align_cp
        iff ((0 <= addr) && (addr + 32 <= DmemSizeByte));

    // See operand_b >= 32. This is grs2 for BN.SID and grd for BN.LID: in either case, it causes an
    // error.
    `DEF_SEEN_CP(bigb_cp, operand_b >= 32)
    `DEF_MNEM_CROSS(bigb)

    // Underflow call stack and set both increments
    `DEF_SEEN_CP(underflow_and_inc_both_cp, call_stack_underflow && inc_both)
    `DEF_MNEM_CROSS(underflow_and_inc_both)

    // Underflow call stack with grs1 and have a bad WDR index in *grd or *grs2 (depending on
    // whether it's BN.LID or BN.SID).
    `DEF_SEEN_CP(underflow_and_badb_cp,
                 call_stack_underflow && (grx2 != 5'd1) && (operand_b >= 32))
    `DEF_MNEM_CROSS(underflow_and_badb)

    // Underflow call stack with grd/grs2 and compute a bad address from *grs1
    `DEF_SEEN_CP(underflow_and_bad_addr_cp,
                 call_stack_underflow &&
                 (grs1 != 5'd1) &&
                 ((0 < addr) || (addr >= DmemSizeByte) || ((addr & 32'd31) != 0)))
    `DEF_MNEM_CROSS(underflow_and_bad_addr)

    // Set both increments and have a bad WDR index in *grd/*grs2.
    `DEF_SEEN_CP(inc_both_and_bad_wdr_cp,
                 inc_both && !call_stack_underflow && (operand_b >= 32))
    `DEF_MNEM_CROSS(inc_both_and_bad_wdr)

    // Set both increments and compute a bad address from *grs1
    `DEF_SEEN_CP(inc_both_and_bad_addr_cp,
                 inc_both &&
                 !call_stack_underflow &&
                 ((0 < addr) || (addr >= DmemSizeByte) || ((addr & 32'd31) != 0)))
    `DEF_MNEM_CROSS(inc_both_and_bad_addr)

    // Have a bad WDR index and also compute a bad address
    `DEF_SEEN_CP(bad_wdr_and_bad_addr_cp,
                 !call_stack_underflow &&
                 (operand_b >= 32) &&
                 ((0 < addr) || (addr >= DmemSizeByte) || ((addr & 32'd31) != 0)))
    `DEF_MNEM_CROSS(bad_wdr_and_bad_addr)

    // Underflow call stack with grs1, set both increments, and have a bad WDR index in *grd/*grs2
    `DEF_SEEN_CP(underflow_and_inc_both_and_bad_wdr_cp,
                 call_stack_underflow &&
                 inc_both &&
                 (grx2 != 5'd1) &&
                 (operand_b >= 32))
    `DEF_MNEM_CROSS(underflow_and_inc_both_and_bad_wdr)

    // Underflow call stack with grd/grs2, set both increments, and compute a bad address from *grs1
    `DEF_SEEN_CP(underflow_and_inc_both_and_bad_addr_cp,
                 call_stack_underflow &&
                 inc_both &&
                 (grs1 != 5'd1) &&
                 ((0 < addr) || (addr >= DmemSizeByte) || ((addr & 32'd31) != 0)))
    `DEF_MNEM_CROSS(underflow_and_inc_both_and_bad_addr)

    // Set both increments, have a bad WDR index and compute a bad address
    `DEF_SEEN_CP(inc_both_and_bad_wdr_and_bad_addr_cp,
                 inc_both &&
                 !call_stack_underflow &&
                 (operand_b >= 32) &&
                 ((0 < addr) || (addr >= DmemSizeByte) || ((addr & 32'd31) != 0)))
    `DEF_MNEM_CROSS(inc_both_and_bad_wdr_and_bad_addr)
  endgroup

  covergroup insn_bn_movr_cg
    with function sample(logic [31:0] operand_a,
                         logic [31:0] operand_b,
                         logic        inc_both,
                         logic [4:0]  grs,
                         logic [4:0]  grd,
                         logic        call_stack_underflow);

    // Underflow call stack and set both increments
    `DEF_SEEN_CP(underflow_and_inc_both_cp, call_stack_underflow && inc_both)

    // Underflow call stack for grs and have a bad WDR index in *grd.
    `DEF_SEEN_CP(underflow_and_bad_grd_cp,
                 call_stack_underflow && (grd != 5'd1) && (operand_b >= 32))

    // Underflow call stack for grd and have a bad WDR index in *grs.
    `DEF_SEEN_CP(underflow_and_bad_grs_cp,
                 call_stack_underflow && (grs != 5'd1) && (operand_a >= 32))

    // Set both increments and have a bad WDR index.
    `DEF_SEEN_CP(inc_both_and_bad_wdr_cp,
                 inc_both &&
                 !call_stack_underflow &&
                 ((operand_a >= 32) || (operand_b >= 32)))

    // Underflow call stack for grs, setting both increments and have a bad WDR index in *grd.
    `DEF_SEEN_CP(underflow_grs_and_inc_both_and_bad_wdr_cp,
                 call_stack_underflow &&
                 inc_both &&
                 (grd != 5'd1) &&
                 (operand_b >= 32))

    // Underflow call stack for grd, setting both increments and have a bad WDR index in *grs.
    `DEF_SEEN_CP(underflow_grd_and_inc_both_and_bad_wdr_cp,
                 call_stack_underflow &&
                 inc_both &&
                 (grs != 5'd1) &&
                 (operand_a >= 32))
  endgroup

  covergroup insn_bn_wsrr_cg
    with function sample(logic [7:0] wsr_imm, logic has_sideload_key);

    // Track coverage of the key sideload WSRs specifically. Here 4 - 7 are the indices of KEY_S0_L,
    // KEY_S0_H, KEY_S1_L and KEY_S1_H respectively.
    key_wsr_cp: coverpoint wsr_imm { bins key_wsrs[] = {[4:7]}; }

    // Crossing key_wsr_cp with has_sideload_key asks that we see a read of each WSR both with and
    // without a valid key.
    key_avail_cross: cross key_wsr_cp, has_sideload_key;

  endgroup

  // A mapping from instruction name to the name of that instruction's encoding.
  string insn_encodings[mnem_str_t];

  function new(string name, uvm_component parent);
    super.new(name, parent);

    ext_csr_cmd_cg = new;
    ext_csr_ctrl_cg = new;
    ext_csr_status_cg = new;
    ext_csr_err_bits_cg = new;
    ext_csr_fatal_alert_cause_cg = new;
    ext_csr_insn_cnt_cg = new;
    ext_csr_load_checksum_wur_cg = new;
    ext_csr_wr_operational_state_cg = new;
    promoted_err_cg = new;
    scratchpad_writes_cg = new;

    bad_internal_state_cg = new;
    internal_intg_err_cg = new;
    insn_addr_cg = new;
    call_stack_cg = new;
    flag_write_cg = new;
    pairwise_insn_cg = new;

    enc_bna_cg = new;
    enc_bnaf_cg = new;
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
    enc_ecall_cg = new;
    enc_i_cg = new;
    enc_is_cg = new;
    enc_j_cg = new;
    enc_loop_cg = new;
    enc_loopi_cg = new;
    enc_r_cg = new;
    enc_s_cg = new;
    enc_wcsr_cg = new;
    enc_u_cg = new;

    insn_addsub_cg = new;
    insn_addi_cg = new;
    insn_sll_cg = new;
    insn_slli_cg = new;
    insn_srl_cg = new;
    insn_srli_cg = new;
    insn_sra_cg = new;
    insn_srai_cg = new;
    insn_log_binop_cg = new;
    insn_xw_cg = new;
    insn_bxx_cg = new;
    insn_jal_cg = new;
    insn_jalr_cg = new;
    insn_csrrs_cg = new;
    insn_csrrw_cg = new;
    insn_loop_cg = new;
    insn_loopi_cg = new;
    insn_bn_addc_cg = new;
    insn_bn_addm_cg = new;
    insn_bn_mulqaccx_cg = new;
    insn_bn_subcmpb_cg = new;
    insn_bn_subm_cg = new;
    insn_bn_xid_cg = new;
    insn_bn_movr_cg = new;
    insn_bn_wsrr_cg = new;

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
    insn_encodings[mnem_ecall]         = "ecall";
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
    insn_encodings[mnem_dummy]         = "dummy";
    insn_encodings[mnem_question_mark] = "dummy";
  endfunction

  // Reset any internal state tracking because the DUT has just seen a reset
  function void on_reset();
    wur_state = WUR_IDLE;
    last_write_state.delete();
    last_err_bits = 0;
    last_mnem = '0;
  endfunction

  // Called on each change of operational state
  function void on_state_change(operational_state_e new_state);
    last_err_bits = 0;
    last_mnem = '0;
    // Sample bad internal state related signals here because otherwise they tend to not get
    // captured.
    bad_internal_state_cg.sample(cfg.trace_vif.urnd_all_zero_q,
                                 cfg.trace_vif.insn_addr_err_q,
                                 cfg.trace_vif.scramble_state_err_q,
                                 cfg.trace_vif.predec_err_q,
                                 cfg.trace_vif.missed_gnt_q,
                                 cfg.trace_vif.controller_bad_int_q,
                                 cfg.trace_vif.start_stop_bad_int_q,
                                 cfg.trace_vif.rf_base_spurious_we_err_q,
                                 cfg.trace_vif.rf_bignum_spurious_we_err_q,
                                 cfg.trace_vif.ext_mubi_err_q);

    internal_intg_err_cg.sample(cfg.trace_vif.internal_intg_err_q);
  endfunction

  function void on_write_to_wr_csr(uvm_reg csr, logic [31:0] data, operational_state_e state);
    // Ignore writes with the value that's there already
    if (data == csr.get_mirrored_value()) return;

    // Otherwise, set an entry in last_write_state
    last_write_state[csr_str_t'(csr.get_name())] = state;
  endfunction

  // Handle coverage for external (bus-accessible) CSRs.
  //
  // This runs just before calling predict to update the RAL model, so the old value of the CSR can
  // be read with csr.get_mirrored_value().
  function void on_ext_csr_access(uvm_reg csr, otbn_env_pkg::access_e access_type,
                                  logic [31:0] data, operational_state_e state);

    csr_str_t csr_name        = csr_str_t'(csr.get_name());
    bit track_write_then_read = 1'b0;

    case (csr_name)
      "cmd": begin
        ext_csr_cmd_cg.sample(otbn_pkg::cmd_e'(data), access_type, state);
      end
      "ctrl": begin
        track_write_then_read = 1'b1;
        ext_csr_ctrl_cg.sample(data[0], access_type, state);
      end
      "status": begin
        ext_csr_status_cg.sample(otbn_pkg::status_e'(data), access_type);
      end
      "err_bits": begin
        last_err_bits = data;
        ext_csr_err_bits_cg.sample(otbn_pkg::err_bits_t'(data),
                                   csr.get_mirrored_value(), access_type, state);
      end
      "fatal_alert_cause": begin
        ext_csr_fatal_alert_cause_cg.sample(data, access_type, state);

        // If we read a FATAL_ALERT_CAUSE of (1 << 7) = FATAL_SOFTWARE and we're in a locked state
        // then we should sample promoted_err_cg to track what SW error was promoted.
        if ((state == OperationalStateLocked) &&
            (access_type == AccessSoftwareRead) &&
            (data == (1 << 7))) begin
          promoted_err_cg.sample(last_err_bits[5:0]);
        end
      end
      "insn_cnt": begin
        ext_csr_insn_cnt_cg.sample(data, csr.get_mirrored_value(), access_type, state);
      end
      "load_checksum": begin
        track_write_then_read = 1'b1;

        // Special handling for the "write; update; read" sequence.
        case (wur_state)
          WUR_IDLE: begin
            // The WUR_IDLE -> WUR_WRITTEN_CSR transition should happen if we see a write to the
            // register that will change its value and we're in an operational state where it will
            // take effect.
            if ((data != csr.get_mirrored_value()) &&
                (access_type == AccessSoftwareWrite) &&
                (state == OperationalStateIdle)) begin
              wur_state = WUR_WRITTEN_CSR;
            end
          end
          WUR_WRITTEN_CSR: begin
            // We can't leave the WUR_WRITTEN_CSR state by accessing the CSR (see on_mem_write())
          end
          WUR_UPDATED_MEM: begin
            // If we read the CSR after updating memory, sample from the covergroup and go back to
            // WUR_IDLE.
            if (access_type == AccessSoftwareRead) begin
              ext_csr_load_checksum_wur_cg.sample();
              wur_state = WUR_IDLE;
            end
          end
          default: `DV_CHECK_FATAL(0)
        endcase
      end
      default: ; // We only track some registers with functional coverage.
    endcase

    // Track "write then read" across operational states
    if (track_write_then_read) begin
      if (access_type == AccessSoftwareWrite) begin
        on_write_to_wr_csr(csr, data, state);
      end else begin
        if (last_write_state.exists(csr_name)) begin
          ext_csr_wr_operational_state_cg.sample(csr_name, last_write_state[csr_name]);
        end
      end
    end
  endfunction

  // Handle coverage for bus writes to memory
  function void on_mem_write(uvm_mem             mem,
                             bit [31:0]          offset,
                             logic [31:0]        data,
                             operational_state_e state);
    // Handle the "write; update; read" sequence for LOAD_CHECKSUM. If we're in the WUR_WRITTEN_CSR
    // state and this write will have an effect (because we're in the idle state), step to
    // WUR_UPDATED_MEM.
    if ((wur_state == WUR_WRITTEN_CSR) && (state == OperationalStateIdle)) begin
      wur_state = WUR_UPDATED_MEM;
    end
  endfunction

  function void on_tl_write(uvm_reg_addr_t addr, logic [31:0] data, operational_state_e state);
    // Track attempted writes to the scratchpad memory
    if (state == OperationalStateIdle) begin
      scratchpad_writes_cg.sample(addr);
    end
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
    logic [31:0] loop_bodysize;
    logic        call_stack_push, call_stack_pop, call_stack_overflow, call_stack_underflow;

    logic signed [31:0] addr;
    logic [9:0]         imm10;
    logic [11:0]        imm12;
    logic [12:0]        imm13;
    logic [14:0]        imm15;
    logic [20:0]        imm21;

    // Since iss_item and rtl_item have come in separately, we do a quick check here to make sure
    // they actually match the same instruction.
    `DV_CHECK_EQ(iss_item.insn_addr, rtl_item.insn_addr)

    // iss_item.mnemonic is a "string". We have to cast this to an integral type (mnem_str_t) to use
    // it for bins in a coverpoint. This type is chosen to be long enough to hold each valid
    // mnemonic, but it can't hurt to make absolutely sure that nothing overflows.
    `DV_CHECK_FATAL(iss_item.mnemonic.len() <= MNEM_STR_LEN)

    mnem = mnem_str_t'(iss_item.mnemonic);
    insn_data = rtl_item.insn_data;

    // Track and catch when we are on the top of the instruction memory and have a straight-line
    // instruction.
    insn_addr_cg.sample(mnem, rtl_item.insn_addr);

    // Call stack tracking. Some instructions want to know whether they are over- or under-flowing
    // the call stack so, as well as sampling in the call_stack_cg covergroup, we also compute those
    // flags which we'll use below.
    call_stack_cg.sample(rtl_item.call_stack_flags, rtl_item.call_stack_fullness);

    call_stack_push = rtl_item.call_stack_flags.push;
    call_stack_pop = rtl_item.call_stack_flags.pop_a | rtl_item.call_stack_flags.pop_b;

    call_stack_overflow = ((rtl_item.call_stack_fullness == StackFull) &&
                           call_stack_push && !call_stack_pop);
    call_stack_underflow = (rtl_item.call_stack_fullness == StackEmpty) && call_stack_pop;

    // Flag set/clear tracking
    for (int fg = 0; fg < 2; fg++) begin
      if (rtl_item.flags_write_valid[fg]) begin
        flag_write_cg.sample(fg[0], rtl_item.flags_read_data[fg], rtl_item.flags_write_data[fg]);
      end
    end

    // Track pairwise instructions. last_mnem is zero if this is the first instruction since
    // starting an operation.
    if (last_mnem != '0) begin
      pairwise_insn_cg.sample(last_mnem, mnem);
    end
    last_mnem = mnem;

    // Per-encoding coverage. First, use insn_encodings to find the encoding for the instruction.
    // Every instruction mnemonic should have an associated encoding schema.
    encoding = insn_encodings[mnem];
    case (encoding)
      "bna":
        enc_bna_cg.sample(mnem, insn_data,
                          rtl_item.wdr_operand_a, rtl_item.wdr_operand_b,
                          rtl_item.flags_write_data, rtl_item.wdr_write_data);
      "bnaf":
        enc_bnaf_cg.sample(mnem, insn_data,
                           rtl_item.wdr_operand_a, rtl_item.wdr_operand_b,
                           rtl_item.flags_write_data);
      "bnai":
        enc_bnai_cg.sample(mnem, insn_data,
                           rtl_item.wdr_operand_a,
                           rtl_item.flags_write_data);
      "bnam":
        enc_bnam_cg.sample(mnem, insn_data, rtl_item.wdr_operand_a, rtl_item.wdr_operand_b);
      "bnan":
        enc_bnan_cg.sample(mnem, insn_data,
                           rtl_item.wdr_operand_a,
                           rtl_item.flags_write_data,
                           rtl_item.wdr_write_data);
      "bnaq":
        enc_bnaq_cg.sample(mnem, insn_data, rtl_item.wdr_operand_a, rtl_item.wdr_operand_b);
      "bnaqs":
        enc_bnaqs_cg.sample(mnem, insn_data,
                            rtl_item.wdr_operand_a, rtl_item.wdr_operand_b,
                            rtl_item.flags_write_data);
      "bnaqw":
        enc_bnaqw_cg.sample(mnem, insn_data,
                            rtl_item.wdr_operand_a, rtl_item.wdr_operand_b,
                            rtl_item.flags_write_data);
      "bnc":
        enc_bnc_cg.sample(mnem, insn_data,
                          rtl_item.wdr_operand_a, rtl_item.wdr_operand_b,
                          rtl_item.flags_write_data);
      "bnmov":
        enc_bnmov_cg.sample(mnem, insn_data, rtl_item.wdr_operand_a);
      "bnmovr":
        enc_bnmovr_cg.sample(mnem, insn_data, rtl_item.gpr_operand_a, rtl_item.gpr_operand_b);
      "bnr":
        enc_bnr_cg.sample(mnem, insn_data, rtl_item.wdr_operand_a, rtl_item.wdr_operand_b);
      "bns":
        enc_bns_cg.sample(mnem, insn_data,
                          rtl_item.wdr_operand_a, rtl_item.wdr_operand_b,
                          rtl_item.flags_read_data);
      "bnxid":
        enc_bnxid_cg.sample(mnem, insn_data, rtl_item.gpr_operand_a, rtl_item.gpr_operand_b);
      "B":
        enc_b_cg.sample(mnem, insn_data, rtl_item.gpr_operand_a, rtl_item.gpr_operand_b);
      "ecall":
        enc_ecall_cg.sample(mnem, insn_data);
      "I":
        enc_i_cg.sample(mnem, insn_data, rtl_item.gpr_operand_a);
      "Is":
        enc_is_cg.sample(mnem, insn_data, rtl_item.gpr_operand_a);
      "J":
        enc_j_cg.sample(mnem, insn_data);
      "loop":
        enc_loop_cg.sample(mnem, insn_data, rtl_item.gpr_operand_a);
      "loopi":
        enc_loopi_cg.sample(mnem, insn_data);
      "R":
        enc_r_cg.sample(mnem, insn_data, rtl_item.gpr_operand_a, rtl_item.gpr_operand_b);
      "S":
        enc_s_cg.sample(mnem, insn_data, rtl_item.gpr_operand_a, rtl_item.gpr_operand_b);
      "U":
        enc_u_cg.sample(mnem, insn_data);
      "wcsr":
        enc_wcsr_cg.sample(mnem, insn_data);
      "dummy":
        // Bad instruction: no encoding-level coverage.
        ;
      default: `dv_fatal($sformatf("Unknown encoding (%0s) for instruction `%0s'", encoding, mnem),
                         `gfn)
    endcase

    // LOOP and LOOPI instructions store bodysize as an immediate in bits 31:20, but shifted by 1
    // (so a bodysize of 1 is encoded as 0 etc.)
    loop_bodysize = 32'(insn_data[31:20]) + 32'd1;

    // Instruction-specific coverage.
    case (mnem)
      mnem_add, mnem_sub:
        insn_addsub_cg.sample(mnem, rtl_item.gpr_operand_a, rtl_item.gpr_operand_b);
      mnem_addi:
        insn_addi_cg.sample(insn_data, rtl_item.gpr_operand_a);
      mnem_sll:
        insn_sll_cg.sample(rtl_item.gpr_operand_a, rtl_item.gpr_operand_b);
      mnem_slli:
        insn_slli_cg.sample(insn_data, rtl_item.gpr_operand_a);
      mnem_srl:
        insn_srl_cg.sample(rtl_item.gpr_operand_a, rtl_item.gpr_operand_b);
      mnem_srli:
        insn_srli_cg.sample(insn_data, rtl_item.gpr_operand_a);
      mnem_sra:
        insn_sra_cg.sample(rtl_item.gpr_operand_a, rtl_item.gpr_operand_b);
      mnem_srai:
        insn_srai_cg.sample(insn_data, rtl_item.gpr_operand_a);
      mnem_and, mnem_andi, mnem_or, mnem_ori, mnem_xor, mnem_xori:
        // This covergroup tracks write data, so we only sample when GRD is nonzero
        if (insn_data[11:7] != 0) begin
          insn_log_binop_cg.sample(mnem, insn_data, rtl_item.gpr_write_data);
        end
      mnem_lw: begin
        imm12 = insn_data[31:20];
        addr = $signed(rtl_item.gpr_operand_a) + $signed(imm12);
        insn_xw_cg.sample(mnem,
                          imm12,
                          insn_data[19:15] /* grs1 */,
                          insn_data[11:7] /* grd */,
                          rtl_item.gpr_operand_a,
                          addr,
                          rtl_item.call_stack_fullness,
                          call_stack_underflow);
      end
      mnem_sw: begin
        imm12 = {insn_data[31:25], insn_data[11:7]};
        addr = $signed(rtl_item.gpr_operand_a) + $signed(imm12);
        insn_xw_cg.sample(mnem,
                          imm12,
                          insn_data[19:15] /* grs1 */,
                          insn_data[24:20] /* grs2 */,
                          rtl_item.gpr_operand_a,
                          addr,
                          rtl_item.call_stack_fullness,
                          call_stack_underflow);
      end
      mnem_beq, mnem_bne: begin
        imm13 = {insn_data[31], insn_data[7], insn_data[30:25], insn_data[11:8], 1'b0};
        addr = $signed(rtl_item.insn_addr) + $signed(imm13);
        insn_bxx_cg.sample(mnem,
                           rtl_item.insn_addr,
                           imm13,
                           rtl_item.gpr_operand_a,
                           rtl_item.gpr_operand_b,
                           addr,
                           rtl_item.at_current_loop_end_insn,
                           call_stack_underflow);
      end
      mnem_jal: begin
        imm21 = {insn_data[31], insn_data[19:12], insn_data[20], insn_data[30:21], 1'b0};
        addr = $signed(rtl_item.insn_addr) + $signed(imm21);
        insn_jal_cg.sample(rtl_item.insn_addr,
                           imm21,
                           addr,
                           rtl_item.at_current_loop_end_insn,
                           call_stack_overflow);
      end
      mnem_jalr: begin
        imm12 = insn_data[31:20];
        addr = $signed(rtl_item.gpr_operand_a) + $signed(imm12);
        insn_jalr_cg.sample(rtl_item.insn_addr,
                            imm12,
                            addr,
                            rtl_item.gpr_operand_a,
                            rtl_item.at_current_loop_end_insn,
                            call_stack_underflow,
                            call_stack_overflow);
      end
      mnem_csrrs:
        insn_csrrs_cg.sample(insn_data,
                             rtl_item.gpr_operand_a,
                             rtl_item.call_stack_fullness);
      mnem_csrrw:
        insn_csrrw_cg.sample(insn_data,
                             rtl_item.call_stack_fullness);
      mnem_loop:
        insn_loop_cg.sample(rtl_item.insn_addr,
                            insn_data,
                            rtl_item.gpr_operand_a,
                            rtl_item.loop_stack_fullness,
                            rtl_item.current_loop_end,
                            loop_bodysize,
                            rtl_item.at_current_loop_end_insn,
                            call_stack_underflow);
      mnem_loopi: begin
        imm10 = {insn_data[19:15], insn_data[11:7]};
        insn_loopi_cg.sample(rtl_item.insn_addr,
                             insn_data,
                             rtl_item.loop_stack_fullness,
                             rtl_item.current_loop_end,
                             imm10,
                             loop_bodysize,
                             rtl_item.at_current_loop_end_insn);
      end
      mnem_bn_addc:
        insn_bn_addc_cg.sample(insn_data,
                               rtl_item.flags_read_data);
      mnem_bn_addm:
        insn_bn_addm_cg.sample(insn_data,
                               rtl_item.wdr_operand_a,
                               rtl_item.wdr_operand_b,
                               rtl_item.mod);
      mnem_bn_mulqacc, mnem_bn_mulqacc_so, mnem_bn_mulqacc_wo:
        insn_bn_mulqaccx_cg.sample(mnem,
                                   rtl_item.new_acc_extended);
      mnem_bn_subb, mnem_bn_cmpb:
        insn_bn_subcmpb_cg.sample(mnem,
                                  insn_data,
                                  rtl_item.flags_read_data);
      mnem_bn_subm:
        insn_bn_subm_cg.sample(insn_data,
                               rtl_item.wdr_operand_a,
                               rtl_item.wdr_operand_b,
                               rtl_item.mod);
      mnem_bn_lid, mnem_bn_sid: begin
        logic       inc_both = insn_data[8] && insn_data[7];
        logic [4:0] grs1 = insn_data[19:15];
        logic [4:0] grx2 = insn_data[24:20]; // Either GRD or GRS2
        logic       local_x1_uflow;

        imm15 = {insn_data[11:9], insn_data[31:25], 5'b0};
        addr = $signed(rtl_item.gpr_operand_a) + $signed(imm15);

        // Compute our own definition of call_stack_underflow. This should match the existing one if
        // !inc_both. However, when both increments are set the RTL decoder squashes the call stack
        // update flags so we have to figure them out ourselves.
        local_x1_uflow = (rtl_item.call_stack_fullness == StackEmpty) &&
                         ((grs1 == 5'd1) || (grx2 == 5'd1));
        `DV_CHECK_FATAL(local_x1_uflow || !call_stack_underflow)
        `DV_CHECK_FATAL(inc_both || call_stack_underflow || !local_x1_uflow)

        insn_bn_xid_cg.sample(mnem,
                              imm15,
                              rtl_item.gpr_operand_a,
                              rtl_item.gpr_operand_b,
                              addr,
                              inc_both,
                              grs1,
                              grx2,
                              local_x1_uflow);
      end
      mnem_bn_movr: begin
        logic       inc_both = insn_data[9] && insn_data[7];
        logic [4:0] grs = insn_data[19:15];
        logic [4:0] grd = insn_data[24:20];
        logic       local_x1_uflow;

        // Compute our own definition of call_stack_underflow. This should match the existing one if
        // !inc_both. However, when both increments are set the RTL decoder squashes the call stack
        // update flags so we have to figure them out ourselves.
        local_x1_uflow = (rtl_item.call_stack_fullness == StackEmpty) &&
                         ((grs == 5'd1) || (grd == 5'd1));
        `DV_CHECK_FATAL(local_x1_uflow || !call_stack_underflow)
        `DV_CHECK_FATAL(inc_both || call_stack_underflow || !local_x1_uflow)

        insn_bn_movr_cg.sample(rtl_item.gpr_operand_a,
                               rtl_item.gpr_operand_b,
                               inc_both,
                               grs,
                               grd,
                               local_x1_uflow);
      end
      mnem_bn_wsrr: begin
        logic [7:0] wsr_imm = insn_data[27:20];
        insn_bn_wsrr_cg.sample(wsr_imm, rtl_item.has_sideload_key);
      end
      default:
        // No special handling for this instruction yet.
        ;
    endcase
  endfunction

`undef DEF_MNEM_BIN
`undef DEF_MNEM_BINS_EXCEPT_ECALL
`undef DEF_MNEM_CROSS
`undef DEF_MNEM_CROSS2
`undef DEF_MNEM_CROSS3
`undef GPR_BIN_TYPES
`undef DEF_GPR_CP
`undef _DEF_TOGGLE_COV_1
`undef _DEF_TOGGLE_COV_2
`undef _DEF_TOGGLE_COV_4
`undef _DEF_TOGGLE_COV_8
`undef _DEF_TOGGLE_COV_16
`undef _DEF_TOGGLE_COV_32
`undef _DEF_TOGGLE_COV_64
`undef _DEF_TOGGLE_COV_128
`undef DEF_GPR_TOGGLE_COV
`undef DEF_WDR_TOGGLE_COV
`undef _DEF_TOGGLE_CROSS_1
`undef _DEF_TOGGLE_CROSS_2
`undef _DEF_TOGGLE_CROSS_4
`undef _DEF_TOGGLE_CROSS_8
`undef _DEF_TOGGLE_CROSS_16
`undef _DEF_TOGGLE_CROSS_32
`undef _DEF_TOGGLE_CROSS_64
`undef _DEF_TOGGLE_CROSS_128
`undef DEF_GPR_TOGGLE_CROSS
`undef DEF_WDR_TOGGLE_CROSS
`undef DEF_SIGN_CP
`undef _NZ_CP_BINS
`undef DEF_NZ_CP
`undef DEF_NZ_IF_CP
`undef DEF_SEEN_CP
`undef DEF_SEEN_IF_CP
`undef DEF_CSR_CP

endclass
