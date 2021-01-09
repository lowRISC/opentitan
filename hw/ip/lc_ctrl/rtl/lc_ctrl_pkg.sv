// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package lc_ctrl_pkg;

  import prim_util_pkg::vbits;
  import lc_ctrl_state_pkg::*;

  /////////////////////////////////
  // General Typedefs and Params //
  /////////////////////////////////

  parameter int LcValueWidth = 16;
  parameter int NumLcStateValues = 12;
  parameter int LcStateWidth = NumLcStateValues * LcValueWidth;
  parameter int NumLcCountValues = 16;
  parameter int LcCountWidth = NumLcCountValues * LcValueWidth;
  parameter int NumLcStates = 13;
  parameter int DecLcStateWidth = vbits(NumLcStates);
  parameter int DecLcCountWidth = vbits(NumLcCountValues+1);
  parameter int LcIdStateWidth = LcValueWidth;
  parameter int DecLcIdStateWidth = 2;

  parameter int LcTokenWidth = 128;
  typedef logic [LcTokenWidth-1:0] lc_token_t;

  typedef enum logic [LcStateWidth-1:0] {
    // Halfword idx   :  11 | 10 |  9 |  8 |  7 |  6 |  5 |  4 |  3 |  2 |  1 |  0
    LcStRaw           = '0,
    LcStTestUnlocked0 = {A11, A10, A9, A8, A7, A6, A5, A4, A3, A2, A1, B0},
    LcStTestLocked0   = {A11, A10, A9, A8, A7, A6, A5, A4, A3, A2, B1, B0},
    LcStTestUnlocked1 = {A11, A10, A9, A8, A7, A6, A5, A4, A3, B2, B1, B0},
    LcStTestLocked1   = {A11, A10, A9, A8, A7, A6, A5, A4, B3, B2, B1, B0},
    LcStTestUnlocked2 = {A11, A10, A9, A8, A7, A6, A5, B4, B3, B2, B1, B0},
    LcStTestLocked2   = {A11, A10, A9, A8, A7, A6, B5, B4, B3, B2, B1, B0},
    LcStTestUnlocked3 = {A11, A10, A9, A8, A7, B6, B5, B4, B3, B2, B1, B0},
    LcStDev           = {A11, A10, A9, A8, B7, B6, B5, B4, B3, B2, B1, B0},
    LcStProd          = {A11, A10, A9, B8, A7, B6, B5, B4, B3, B2, B1, B0},
    LcStProdEnd       = {A11, A10, B9, A8, A7, B6, B5, B4, B3, B2, B1, B0},
    LcStRma           = {B11, B10, A9, B8, B7, B6, B5, B4, B3, B2, B1, B0},
    LcStScrap         = {B11, B10, B9, B8, B7, B6, B5, B4, B3, B2, B1, B0}
  } lc_state_e;

  // Decoded life cycle state, used to interface with CSRs and TAP.
  typedef enum logic [DecLcStateWidth-1:0] {
    DecLcStRaw            = 4'h0,
    DecLcStTestUnlocked0  = 4'h1,
    DecLcStTestLocked0    = 4'h2,
    DecLcStTestUnlocked1  = 4'h3,
    DecLcStTestLocked1    = 4'h4,
    DecLcStTestUnlocked2  = 4'h5,
    DecLcStTestLocked2    = 4'h6,
    DecLcStTestUnlocked3  = 4'h7,
    DecLcStDev            = 4'h8,
    DecLcStProd           = 4'h9,
    DecLcStProdEnd        = 4'hA,
    DecLcStRma            = 4'hB,
    DecLcStScrap          = 4'hC,
    DecLcStPostTrans      = 4'hD,
    DecLcStEscalate       = 4'hE,
    DecLcStInvalid        = 4'hF
  } dec_lc_state_e;

  typedef enum logic [LcIdStateWidth-1:0] {
    LcIdBlank        = E0,
    LcIdPersonalized = F0
  } lc_id_state_e;

  typedef enum logic [DecLcIdStateWidth-1:0] {
    DecLcIdBlank        = 2'd0,
    DecLcIdPersonalized = 2'd1,
    DecLcIdInvalid      = 2'd2
  } dec_lc_id_state_e;

  typedef enum logic [LcCountWidth-1:0] {
    LcCntRaw = '0,
    LcCnt1   = {C15, C14, C13, C12, C11, C10, C9, C8, C7, C6, C5, C4, C3, C2, C1, D0},
    LcCnt2   = {C15, C14, C13, C12, C11, C10, C9, C8, C7, C6, C5, C4, C3, C2, D1, D0},
    LcCnt3   = {C15, C14, C13, C12, C11, C10, C9, C8, C7, C6, C5, C4, C3, D2, D1, D0},
    LcCnt4   = {C15, C14, C13, C12, C11, C10, C9, C8, C7, C6, C5, C4, D3, D2, D1, D0},
    LcCnt5   = {C15, C14, C13, C12, C11, C10, C9, C8, C7, C6, C5, D4, D3, D2, D1, D0},
    LcCnt6   = {C15, C14, C13, C12, C11, C10, C9, C8, C7, C6, D5, D4, D3, D2, D1, D0},
    LcCnt7   = {C15, C14, C13, C12, C11, C10, C9, C8, C7, D6, D5, D4, D3, D2, D1, D0},
    LcCnt8   = {C15, C14, C13, C12, C11, C10, C9, C8, D7, D6, D5, D4, D3, D2, D1, D0},
    LcCnt9   = {C15, C14, C13, C12, C11, C10, C9, D8, D7, D6, D5, D4, D3, D2, D1, D0},
    LcCnt10  = {C15, C14, C13, C12, C11, C10, D9, D8, D7, D6, D5, D4, D3, D2, D1, D0},
    LcCnt11  = {C15, C14, C13, C12, C11, D10, D9, D8, D7, D6, D5, D4, D3, D2, D1, D0},
    LcCnt12  = {C15, C14, C13, C12, D11, D10, D9, D8, D7, D6, D5, D4, D3, D2, D1, D0},
    LcCnt13  = {C15, C14, C13, D12, D11, D10, D9, D8, D7, D6, D5, D4, D3, D2, D1, D0},
    LcCnt14  = {C15, C14, D13, D12, D11, D10, D9, D8, D7, D6, D5, D4, D3, D2, D1, D0},
    LcCnt15  = {C15, D14, D13, D12, D11, D10, D9, D8, D7, D6, D5, D4, D3, D2, D1, D0},
    LcCnt16  = {D15, D14, D13, D12, D11, D10, D9, D8, D7, D6, D5, D4, D3, D2, D1, D0}
  } lc_cnt_e;

  typedef logic [DecLcCountWidth-1:0] dec_lc_cnt_t;


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
  } lc_tx_e;

  typedef lc_tx_e lc_tx_t;

  parameter lc_tx_t LC_TX_DEFAULT = Off;

  parameter int RmaSeedWidth = 32;
  typedef logic [RmaSeedWidth-1:0] lc_flash_rma_seed_t;

  parameter int LcKeymgrDivWidth = 64;
  typedef logic [LcKeymgrDivWidth-1:0] lc_keymgr_div_t;

  ////////////////////
  // Main FSM State //
  ////////////////////

  // Encoding generated with:
  // $ ./sparse-fsm-encode.py -d 5 -m 14 -n 16 \
  //      -s 2934212379 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||| (6.59%)
  //  6: |||||||||| (10.99%)
  //  7: |||||||||||||||| (17.58%)
  //  8: |||||||||||||||||||| (20.88%)
  //  9: |||||||||||||||| (17.58%)
  // 10: |||||||||||||| (15.38%)
  // 11: |||||| (6.59%)
  // 12: ||| (3.30%)
  // 13: | (1.10%)
  // 14: --
  // 15: --
  // 16: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 13
  //
  localparam int FsmStateWidth = 16;
  typedef enum logic [FsmStateWidth-1:0] {
    ResetSt       = 16'b1100000001111011,
    IdleSt        = 16'b1111011010111100,
    ClkMuxSt      = 16'b0000011110101101,
    CntIncrSt     = 16'b1100111011001001,
    CntProgSt     = 16'b0011001111000111,
    TransCheckSt  = 16'b0000110001010100,
    TokenHashSt   = 16'b1110100010001111,
    FlashRmaSt    = 16'b0110111010110000,
    TokenCheck0St = 16'b0010000011000000,
    TokenCheck1St = 16'b1101010101101111,
    TransProgSt   = 16'b1000000110101011,
    PostTransSt   = 16'b0110110100101100,
    EscalateSt    = 16'b1010100001010001,
    InvalidSt     = 16'b1011110110011011
  } fsm_state_e;

  ///////////////////////////////////////////
  // Manufacturing State Transition Matrix //
  ///////////////////////////////////////////

  // The token index matrix below encodes 1) which transition edges are valid and 2) which token
  // to use for a given transition edge. Note that unconditional but otherwise valid transitions
  // are assigned the ZeroTokenIdx, whereas invalid transitions are assigned an InvalidTokenIdx.
  parameter token_idx_e [NumLcStates-1:0][NumLcStates-1:0] TransTokenIdxMatrix = {
    // SCRAP
    {13{InvalidTokenIdx}}, // -> TEST_LOCKED0-2, TEST_UNLOCKED0-3, DEV, PROD, PROD_END, RMA, SCRAP
    // RMA
    ZeroTokenIdx,          // -> SCRAP
    {12{InvalidTokenIdx}}, // -> TEST_LOCKED0-2, TEST_UNLOCKED0-3, DEV, PROD, PROD_END, RMA
    // PROD_END
    ZeroTokenIdx,          // -> SCRAP
    {12{InvalidTokenIdx}}, // -> TEST_LOCKED0-2, TEST_UNLOCKED0-3, DEV, PROD, PROD_END, RMA
    // PROD
    ZeroTokenIdx,          // -> SCRAP
    RmaTokenIdx,           // -> RMA
    {11{InvalidTokenIdx}}, // -> TEST_LOCKED0-2, TEST_UNLOCKED0-3, DEV, PROD, PROD_END
    // DEV
    ZeroTokenIdx,          // -> SCRAP
    RmaTokenIdx,           // -> RMA
    {11{InvalidTokenIdx}}, // -> TEST_LOCKED0-2, TEST_UNLOCKED0-3, DEV, PROD, PROD_END
    // TEST_UNLOCKED3
    {2{ZeroTokenIdx}},     // -> SCRAP, RMA
    {3{TestExitTokenIdx}}, // -> PROD, PROD_END, DEV
    {8{InvalidTokenIdx}},  // -> TEST_LOCKED0-2, TEST_UNLOCKED0-3, RAW
    // TEST_LOCKED2
    ZeroTokenIdx,          // -> SCRAP
    InvalidTokenIdx,       // -> RMA
    {3{TestExitTokenIdx}}, // -> PROD, PROD_END, DEV
    TestUnlockTokenIdx,    // -> TEST_UNLOCKED3
    {7{InvalidTokenIdx}},  // -> TEST_LOCKED0-2, TEST_UNLOCKED0-2, RAW
    // TEST_UNLOCKED2
    {2{ZeroTokenIdx}},     // -> SCRAP, RMA
    {3{TestExitTokenIdx}}, // -> PROD, PROD_END, DEV
    InvalidTokenIdx,       // -> TEST_UNLOCKED3
    ZeroTokenIdx,          // -> TEST_LOCKED2
    {6{InvalidTokenIdx}},  // -> TEST_LOCKED0-1, TEST_UNLOCKED0-2, RAW
    // TEST_LOCKED1
    ZeroTokenIdx,          // -> SCRAP
    InvalidTokenIdx,       // -> RMA
    {3{TestExitTokenIdx}}, // -> PROD, PROD_END, DEV
    TestUnlockTokenIdx,    // -> TEST_UNLOCKED3
    InvalidTokenIdx  ,     // -> TEST_LOCKED2
    TestUnlockTokenIdx,    // -> TEST_UNLOCKED2
    {5{InvalidTokenIdx}},  // -> TEST_LOCKED0-1, TEST_UNLOCKED0-1, RAW
    // TEST_UNLOCKED1
    {2{ZeroTokenIdx}},     // -> SCRAP, RMA
    {3{TestExitTokenIdx}}, // -> PROD, PROD_END, DEV
    InvalidTokenIdx,       // -> TEST_UNLOCKED3
    ZeroTokenIdx,          // -> TEST_LOCKED2
    InvalidTokenIdx,       // -> TEST_UNLOCKED2
    ZeroTokenIdx,          // -> TEST_LOCKED1
    {4{InvalidTokenIdx}},  // -> TEST_LOCKED0, TEST_UNLOCKED0-1, RAW
    // TEST_LOCKED0
    ZeroTokenIdx,          // -> SCRAP
    InvalidTokenIdx,       // -> RMA
    {3{TestExitTokenIdx}}, // -> PROD, PROD_END, DEV
    TestUnlockTokenIdx,    // -> TEST_UNLOCKED3
    InvalidTokenIdx,       // -> TEST_LOCKED2
    TestUnlockTokenIdx,    // -> TEST_UNLOCKED2
    InvalidTokenIdx,       // -> TEST_LOCKED1
    TestUnlockTokenIdx,    // -> TEST_UNLOCKED1
    {3{InvalidTokenIdx}},  // -> TEST_LOCKED0, TEST_UNLOCKED0, RAW
    // TEST_UNLOCKED0
    {2{ZeroTokenIdx}},     // -> SCRAP, RMA
    {3{TestExitTokenIdx}}, // -> PROD, PROD_END, DEV
    InvalidTokenIdx,       // -> TEST_UNLOCKED3
    ZeroTokenIdx,          // -> TEST_LOCKED2
    InvalidTokenIdx,       // -> TEST_UNLOCKED2
    ZeroTokenIdx,          // -> TEST_LOCKED1
    InvalidTokenIdx,       // -> TEST_UNLOCKED1
    ZeroTokenIdx,          // -> TEST_LOCKED0
    {2{InvalidTokenIdx}},  // -> TEST_UNLOCKED0, RAW
    // RAW
    ZeroTokenIdx,          // -> SCRAP
    {4{InvalidTokenIdx}},  // -> RMA, PROD, PROD_END, DEV
    RawUnlockTokenIdx,     // -> TEST_UNLOCKED3
    InvalidTokenIdx,       // -> TEST_LOCKED2
    RawUnlockTokenIdx,     // -> TEST_UNLOCKED2
    InvalidTokenIdx,       // -> TEST_LOCKED1
    RawUnlockTokenIdx,     // -> TEST_UNLOCKED1
    InvalidTokenIdx,       // -> TEST_LOCKED0
    RawUnlockTokenIdx,     // -> TEST_UNLOCKED0
    InvalidTokenIdx        // -> RAW
  };

endpackage : lc_ctrl_pkg
