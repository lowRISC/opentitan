// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package cheriot_pkg;

  // Encoding generated at commit 1eb8139d51 using Python 3.10.19 with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv \
  //     --seed 492361 --distance 4 --states 3 --bits 6
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
  //
  // Minimum Hamming distance: 4
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 5
  //
  localparam int SwitchStateWidth = 6;
  typedef enum logic [SwitchStateWidth-1:0] {
    Unlocked  = 6'b010110,
    LockedEna = 6'b100101,
    LockedDis = 6'b111011,
    Error     = 6'b001000
  } switch_state_e;

endpackage
