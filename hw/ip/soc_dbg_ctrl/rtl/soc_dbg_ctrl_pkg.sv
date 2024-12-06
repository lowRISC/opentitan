// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package soc_dbg_ctrl_pkg;
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 4 -m 8 -n 7 \
  //     -s 29565098 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: |||||||||||||||||||| (100.00%)
  //  5: --
  //  6: --
  //  7: --
  //
  // Minimum Hamming distance: 4
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 6
  //
  localparam int DbgCategoryWidth = 7;
  typedef enum logic [DbgCategoryWidth-1:0] {
    DbgCategoryLocked  = 7'b1010000,
    DbgCategory2       = 7'b1001101,
    DbgCategory3       = 7'b0001010,
    DbgCategory4       = 7'b1100011,
    // Reserved for future usage
    DbgCategoryUnused0 = 7'b0111001,
    DbgCategoryUnused1 = 7'b1111110,
    DbgCategoryUnused2 = 7'b0100100,
    DbgCategoryUnused3 = 7'b0010111
  } dbg_category_e;

  // Debug policy bus distributed in the SoC
  typedef struct packed {
    prim_mubi_pkg::mubi4_t valid;
    dbg_category_e         category;
    prim_mubi_pkg::mubi4_t relocked;
  } soc_dbg_policy_t;

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 6 -n 6 \
  //     -s 1870242553 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (53.33%)
  //  4: ||||||||||||||||| (46.67%)
  //  5: --
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 5
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
      Idle                = 6'b101000,
      CheckLifecycleState = 6'b011101,
      Wait4DftEn          = 6'b000110,
      CheckHaltPin        = 6'b110011,
      CheckJtagGo         = 6'b111110,
      HaltDone            = 6'b100101
  } halt_state_e;

endpackage
