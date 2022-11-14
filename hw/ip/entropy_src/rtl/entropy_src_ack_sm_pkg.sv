// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// State definitions for entropy_src_ack_sm, provided as a separate package for use in DV

package entropy_src_ack_sm_pkg;

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 3 -n 6 \
  //      -s 1236774883 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (33.33%)
  //  4: |||||||||||||||||||| (33.33%)
  //  5: |||||||||||||||||||| (33.33%)
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 5
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 4
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    Idle  = 6'b011101, // idle
    Wait  = 6'b101100, // wait until the fifo has an entry
    Error = 6'b000010  // illegal state reached and hang
  } state_e;

endpackage
