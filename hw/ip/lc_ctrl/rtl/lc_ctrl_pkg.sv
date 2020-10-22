// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package lc_ctrl_pkg;

  /////////////////////////////////
  // General Typedefs and Params //
  /////////////////////////////////

  parameter int LcValueWidth = 16;
  parameter int LcTokenWidth = 128;
  parameter int NumLcStateValues = 12;
  parameter int LcStateWidth = NumLcStateValues * LcValueWidth;
  parameter int NumLcCountValues = 32;
  parameter int LcCountWidth = NumLcCountValues * LcValueWidth;

  typedef enum logic [LcValueWidth-1:0] {
    Blk = 16'h0000, // blank
    Set = 16'hF5FA  // programmed
  } lc_value_e;

  typedef enum logic [LcStateWidth-1:0] {
    // Halfword idx   :  11 | 10 |  9 |  8 |  7 |  6 |  5 |  4 |  3 |  2 |  1 |  0
    LcStRaw           = {Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk},
    LcStTestUnlocked0 = {Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Set},
    LcStTestLocked0   = {Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Set, Set},
    LcStTestUnlocked1 = {Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Set, Set, Set},
    LcStTestLocked1   = {Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Set, Set, Set, Set},
    LcStTestUnlocked2 = {Blk, Blk, Blk, Blk, Blk, Blk, Blk, Set, Set, Set, Set, Set},
    LcStTestLocked2   = {Blk, Blk, Blk, Blk, Blk, Blk, Set, Set, Set, Set, Set, Set},
    LcStTestUnlocked3 = {Blk, Blk, Blk, Blk, Blk, Set, Set, Set, Set, Set, Set, Set},
    LcStDev           = {Blk, Blk, Blk, Blk, Set, Set, Set, Set, Set, Set, Set, Set},
    LcStProd          = {Blk, Blk, Blk, Set, Blk, Set, Set, Set, Set, Set, Set, Set},
    LcStProdEnd       = {Blk, Blk, Set, Blk, Blk, Set, Set, Set, Set, Set, Set, Set},
    LcStRma           = {Set, Set, Blk, Set, Set, Set, Set, Set, Set, Set, Set, Set},
    LcStScrap         = {Set, Set, Set, Set, Set, Set, Set, Set, Set, Set, Set, Set}
  } lc_state_e;

  typedef lc_value_e [NumLcCountValues-1:0] lc_cnt_t;

  ////////////////////////////////
  // Typedefs for LC Interfaces //
  ////////////////////////////////

  parameter int TxWidth = 4;
  typedef enum logic [TxWidth-1:0] {
    On  = 4'b1010,
    Off = 4'b0101
  } lc_tx_e;

  typedef struct packed {
    lc_tx_e state;
  } lc_tx_t;

  parameter lc_tx_t LC_TX_DEFAULT = Off;

endpackage : lc_ctrl_pkg
