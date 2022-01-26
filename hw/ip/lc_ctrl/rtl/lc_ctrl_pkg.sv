// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

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

  ////////////////////////////////
  // Typedefs for LC Interfaces //
  ////////////////////////////////

  parameter int TxWidth = 4;

  typedef enum logic [TxWidth-1:0] {
    On  = 4'b1010,
    Off = 4'b0101
  } lc_tx_t;
  parameter lc_tx_t LC_TX_DEFAULT = lc_tx_t'(Off);

  parameter int RmaSeedWidth = 32;
  typedef logic [RmaSeedWidth-1:0] lc_flash_rma_seed_t;
  parameter lc_flash_rma_seed_t LC_FLASH_RMA_SEED_DEFAULT = '0;

  parameter int LcKeymgrDivWidth = 128;
  typedef logic [LcKeymgrDivWidth-1:0] lc_keymgr_div_t;

  ////////////////////
  // Main FSM State //
  ////////////////////

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
