// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

`include "prim_assert.sv"

package lc_ctrl_pkg;

  import prim_util_pkg::vbits;
  import lc_ctrl_state_pkg::*;

  ///////////////////////////////////////
  // Netlist Constants (Hashed Tokens) //
  ///////////////////////////////////////

  parameter int NumTokens = 6;
  parameter int TokenIdxWidth = vbits(NumTokens);
  typedef enum logic [TokenIdxWidth-1:0] {
    // This is the index for the hashed all-zero constant.
    // All unconditional transitions use this token.
    ZeroTokenIdx       = 3'h0,
    RawUnlockTokenIdx  = 3'h1,
    TestUnlockTokenIdx = 3'h2,
    TestExitTokenIdx   = 3'h3,
    RmaTokenIdx        = 3'h4,
    // This is the index for an all-zero value (i.e., hashed value = '0).
    // This is used as an additional blocker for some invalid state transition edges.
    InvalidTokenIdx    = 3'h5
  } token_idx_e;

  parameter int TokenMuxBits = 2**TokenIdxWidth*LcTokenWidth;
  typedef logic [TokenMuxBits-1:0] lc_token_mux_t;

  ////////////////////////////////
  // Typedefs for LC Interfaces //
  ////////////////////////////////

  parameter int TxWidth = 4;

  // Note that changing this encoding has implications on isolation cell
  // values in RTL. Do not change this unless absolutely needed.
  typedef enum logic [TxWidth-1:0] {
    On  = 4'b0101,
    Off = 4'b1010
  } lc_tx_t;
  parameter lc_tx_t LC_TX_DEFAULT = lc_tx_t'(Off);

  parameter int RmaSeedWidth = 32;
  typedef logic [RmaSeedWidth-1:0] lc_flash_rma_seed_t;
  parameter lc_flash_rma_seed_t LC_FLASH_RMA_SEED_DEFAULT = '0;

  parameter int LcKeymgrDivWidth = 128;
  typedef logic [LcKeymgrDivWidth-1:0] lc_keymgr_div_t;

  typedef struct packed {
    logic [lc_ctrl_reg_pkg::HwRevFieldWidth-1:0] chip_gen;
    logic [lc_ctrl_reg_pkg::HwRevFieldWidth-1:0] chip_rev;
  } lc_hw_rev_t;

  /////////////////////////////////////////////
  // Helper Functions for Life Cycle Signals //
  /////////////////////////////////////////////

  // This is a prerequisite for the multibit functions below to work.
  `ASSERT_STATIC_IN_PACKAGE(CheckLcTxValsComplementary_A, On == ~Off)
  // Check for bit-width matching between lc_tx_t and mubi4_t
  `ASSERT_STATIC_IN_PACKAGE(LcMuBiWidthCheck_A, $bits(TxWidth) == $bits(prim_mubi_pkg::MuBi4Width))

  // Convert a life cycle signal to mubi4
  // If in the future other versions are desired, this should really be
  // moved to prim_mubi_pkg
  //
  // The On ^ MuBi4True determines the bit differences between
  // an lc_ctrl_pkg::On and prim_mubi_pkg::MuBi4True.
  // Once the required inversions are determined, it is then applied
  // to the incoming value.  If the incoming value is true, it will
  // appropriately flip to the correct MuBiValue.
  // Since the false value is always complement of the true value,
  // this mechanism will also work for the other polarity.
  function automatic prim_mubi_pkg::mubi4_t lc_to_mubi4(lc_tx_t val);
    return prim_mubi_pkg::mubi4_t'(val ^ (On ^ prim_mubi_pkg::MuBi4True));
  endfunction : lc_to_mubi4

  function automatic lc_tx_t mubi4_to_lc(prim_mubi_pkg::mubi4_t val);
    return lc_tx_t'(val ^ (prim_mubi_pkg::MuBi4True ^ On));
  endfunction : mubi4_to_lc

  // same function as above, but for an input that is MuBi4True, return Off
  // for an input that is MuBi4False, return On
  function automatic lc_tx_t mubi4_to_lc_inv(prim_mubi_pkg::mubi4_t val);
    return lc_tx_t'(val ^ (prim_mubi_pkg::MuBi4True ^ Off));
  endfunction : mubi4_to_lc_inv

  // Test whether the value is supplied is one of the valid enumerations
  function automatic logic lc_tx_test_invalid(lc_tx_t val);
    return ~(val inside {On, Off});
  endfunction : lc_tx_test_invalid

  // Convert a 1 input value to a lc_tx output
  function automatic lc_tx_t lc_tx_bool_to_lc_tx(logic val);
    return (val ? On : Off);
  endfunction : lc_tx_bool_to_lc_tx

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic lc_tx_test_true_strict(lc_tx_t val);
    return On == val;
  endfunction : lc_tx_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic lc_tx_test_false_strict(lc_tx_t val);
    return Off == val;
  endfunction : lc_tx_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic lc_tx_test_true_loose(lc_tx_t val);
    return Off != val;
  endfunction : lc_tx_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic lc_tx_test_false_loose(lc_tx_t val);
    return On != val;
  endfunction : lc_tx_test_false_loose


  // Performs a logical OR operation between two multibit values.
  // This treats "act" as logical 1, and all other values are
  // treated as 0. Truth table:
  //
  // A    | B    | OUT
  //------+------+-----
  // !act | !act | !act
  // act  | !act | act
  // !act | act  | act
  // act  | act  | act
  //
  // Note: due to the nature of the lc_tx_or() function, it is possible that two
  // non-strictly "act" values may produce a strictly "act" value. If this is
  // of concern, e.g. if the output is consumed with a strict check on "act",
  // consider using the prim_lc_or_hardened primitive instead.
  function automatic lc_tx_t lc_tx_or(lc_tx_t a, lc_tx_t b, lc_tx_t act);
    logic [TxWidth-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < TxWidth; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] || b_in[k];
      end else begin
        out[k] = a_in[k] && b_in[k];
      end
    end
    return lc_tx_t'(out);
  endfunction : lc_tx_or

  // Performs a logical AND operation between two multibit values.
  // This treats "act" as logical 1, and all other values are
  // treated as 0. Truth table:
  //
  // A    | B    | OUT
  //------+------+-----
  // !act | !act | !act
  // act  | !act | !act
  // !act | act  | !act
  // act  | act  | act
  //
  // Noite: The lc_tx_and() function does not suffer from the strictness problem
  // that the lc_tx_or function above does, since only one output value in the
  // truth table is strictly "act". It can hence be used in most scenarios without issues.
  // If however the lc_tx_and() function should be strictly rectifying (i.e., only
  // output "act" or ~"act"), the prim_lc_and_hardened can be used.
  function automatic lc_tx_t lc_tx_and(lc_tx_t a, lc_tx_t b, lc_tx_t act);
    logic [TxWidth-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < TxWidth; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] && b_in[k];
      end else begin
        out[k] = a_in[k] || b_in[k];
      end
    end
    return lc_tx_t'(out);
  endfunction : lc_tx_and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic lc_tx_t lc_tx_or_hi(lc_tx_t a, lc_tx_t b);
    return lc_tx_or(a, b, On);
  endfunction : lc_tx_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic lc_tx_t lc_tx_and_hi(lc_tx_t a, lc_tx_t b);
    return lc_tx_and(a, b, On);
  endfunction : lc_tx_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic lc_tx_t lc_tx_or_lo(lc_tx_t a, lc_tx_t b);
    return lc_tx_or(a, b, Off);
  endfunction : lc_tx_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic lc_tx_t lc_tx_and_lo(lc_tx_t a, lc_tx_t b);
    return lc_tx_and(a, b, Off);
  endfunction : lc_tx_and_lo

  // Inverts the logical meaning of the multibit value.
  function automatic lc_tx_t lc_tx_inv(lc_tx_t a);
    return lc_tx_t'(~TxWidth'(a));
  endfunction : lc_tx_inv

  ////////////////////
  // Main FSM State //
  ////////////////////

  // SEC_CM: MAIN.FSM.SPARSE
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 15 -n 16 \
  //      -s 2934212379 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: ||||||| (7.62%)
  //  6: ||||||||| (9.52%)
  //  7: |||||||||||||||| (17.14%)
  //  8: |||||||||||||||||||| (20.95%)
  //  9: ||||||||||||||||| (18.10%)
  // 10: ||||||||||||| (14.29%)
  // 11: |||||| (6.67%)
  // 12: ||| (3.81%)
  // 13: | (1.90%)
  // 14: --
  // 15: --
  // 16: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 13
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 11
  //
  localparam int FsmStateWidth = 16;
  typedef enum logic [FsmStateWidth-1:0] {
    ResetSt       = 16'b1111011010111100,
    IdleSt        = 16'b0000011110101101,
    ClkMuxSt      = 16'b1100111011001001,
    CntIncrSt     = 16'b0011001111000111,
    CntProgSt     = 16'b0000110001010100,
    TransCheckSt  = 16'b0110111010110000,
    TokenHashSt   = 16'b1101001000111111,
    FlashRmaSt    = 16'b1110100010001111,
    TokenCheck0St = 16'b0010000011000000,
    TokenCheck1St = 16'b1101010101101111,
    TransProgSt   = 16'b1000000110101011,
    PostTransSt   = 16'b0110110100101100,
    ScrapSt       = 16'b1010100001010001,
    EscalateSt    = 16'b1011110110011011,
    InvalidSt     = 16'b0011000101001100
  } fsm_state_e;

  ///////////////////////////////////////////
  // Manufacturing State Transition Matrix //
  ///////////////////////////////////////////

  // Helper macro to assemble the token index matrix below.
  // From TEST_UNLOCKED(N)
  // -> SCRAP, RMA
  // -> PROD, PROD_END, DEV
  // -> TEST_UNLOCKED(N+1)-7
  // -> TEST_LOCKED(N)-6
  // -> TEST_UNLOCKED0-(N), RAW
  `define TEST_UNLOCKED(idx)         \
        {2{ZeroTokenIdx}},           \
        {3{TestExitTokenIdx}},       \
        {(7-idx){InvalidTokenIdx,    \
                 ZeroTokenIdx}},     \
        {(2*idx+2){InvalidTokenIdx}}

  // Helper macro to assemble the token index matrix below.
  // From TEST_LOCKED(N)
  // -> SCRAP
  // -> RMA
  // -> PROD, PROD_END, DEV
  // -> TEST_UNLOCKED(N+1)-7
  // -> TEST_LOCKED(N)-6
  // -> TEST_UNLOCKED0-(N), RAW
  `define TEST_LOCKED(idx)         \
      ZeroTokenIdx,                \
      InvalidTokenIdx,             \
      {3{TestExitTokenIdx}},       \
      {(7-idx){TestUnlockTokenIdx, \
               InvalidTokenIdx}},  \
      {(2*idx+2){InvalidTokenIdx}}

  // The token index matrix below encodes 1) which transition edges are valid and 2) which token
  // to use for a given transition edge. Note that unconditional but otherwise valid transitions
  // are assigned the ZeroTokenIdx, whereas invalid transitions are assigned an InvalidTokenIdx.
  parameter token_idx_e [NumLcStates-1:0][NumLcStates-1:0] TransTokenIdxMatrix = {
    // SCRAP
    {21{InvalidTokenIdx}}, // -> TEST_LOCKED0-6, TEST_UNLOCKED0-7, DEV, PROD, PROD_END, RMA, SCRAP
    // RMA
    ZeroTokenIdx,          // -> SCRAP
    {20{InvalidTokenIdx}}, // -> TEST_LOCKED0-6, TEST_UNLOCKED0-7, DEV, PROD, PROD_END, RMA
    // PROD_END
    ZeroTokenIdx,          // -> SCRAP
    {20{InvalidTokenIdx}}, // -> TEST_LOCKED0-6, TEST_UNLOCKED0-7, DEV, PROD, PROD_END, RMA
    // PROD
    ZeroTokenIdx,          // -> SCRAP
    RmaTokenIdx,           // -> RMA
    {19{InvalidTokenIdx}}, // -> TEST_LOCKED0-6, TEST_UNLOCKED0-7, DEV, PROD, PROD_END
    // DEV
    ZeroTokenIdx,          // -> SCRAP
    RmaTokenIdx,           // -> RMA
    {19{InvalidTokenIdx}}, // -> TEST_LOCKED0-6, TEST_UNLOCKED0-7, DEV, PROD, PROD_END
    // TEST_UNLOCKED0-7, TEST_LOCKED0-6
    `TEST_UNLOCKED(7),
    `TEST_LOCKED(6),
    `TEST_UNLOCKED(6),
    `TEST_LOCKED(5),
    `TEST_UNLOCKED(5),
    `TEST_LOCKED(4),
    `TEST_UNLOCKED(4),
    `TEST_LOCKED(3),
    `TEST_UNLOCKED(3),
    `TEST_LOCKED(2),
    `TEST_UNLOCKED(2),
    `TEST_LOCKED(1),
    `TEST_UNLOCKED(1),
    `TEST_LOCKED(0),
    `TEST_UNLOCKED(0),
    // RAW
    ZeroTokenIdx,          // -> SCRAP
    {4{InvalidTokenIdx}},  // -> RMA, PROD, PROD_END, DEV
    {8{RawUnlockTokenIdx,  // -> TEST_UNLOCKED0-7
       InvalidTokenIdx}}   // -> RAW, TEST_LOCKED0-6
  };

  // These macros are only used locally.
  `undef TEST_LOCKED
  `undef TEST_UNLOCKED

endpackage : lc_ctrl_pkg
