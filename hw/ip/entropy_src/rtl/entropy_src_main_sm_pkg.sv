// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// State definitions for entropy_src_main_sm, provided as a separate package for use in DV

package entropy_src_main_sm_pkg;

// Encoding generated with:
// $ ./util/design/sparse-fsm-encode.py -d 3 -m 21 -n 9 \
//      -s 2359261201 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: |||||||||||| (19.05%)
//  4: |||||||||||||||||||| (30.48%)
//  5: ||||||||||||||||| (26.19%)
//  6: |||||||||| (15.71%)
//  7: ||| (5.71%)
//  8: | (2.38%)
//  9:  (0.48%)
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 9
// Minimum Hamming weight: 1
// Maximum Hamming weight: 8
//

  localparam int StateWidth = 9;

  typedef enum logic [StateWidth-1:0] {
    Idle              = 9'b011110101, // idle
    BootHTRunning     = 9'b111010010, // boot mode, wait for health test done pulse
    BootPostHTChk     = 9'b101101110, // boot mode, wait for post health test packer not empty state
    BootPhaseDone     = 9'b010001110, // boot mode, stay here until master enable is off
    StartupHTStart    = 9'b000101100, // startup mode, pulse the sha3 start input
    StartupPhase1     = 9'b100000001, // startup mode, look for first test pass/fail
    StartupPass1      = 9'b110100101, // startup mode, look for first test pass/fail, done if pass
    StartupFail1      = 9'b000010111, // startup mode, look for second fail, alert if fail
    ContHTStart       = 9'b001000000, // continuous test mode, pulse the sha3 start input
    ContHTRunning     = 9'b110100010, // continuous test mode, wait for health test done pulse
    FWInsertStart     = 9'b011000011, // fw ov mode, start the sha3 block
    FWInsertMsg       = 9'b001011001, // fw ov mode, insert fw message into sha3 block
    Sha3MsgDone       = 9'b100001111, // sha3 mode, all input messages added, ready to process
    Sha3Prep          = 9'b011111000, // sha3 mode, request csrng arb to reduce power
    Sha3Process       = 9'b010111111, // sha3 mode, pulse the sha3 process input
    Sha3Valid         = 9'b101110001, // sha3 mode, wait for sha3 valid indication
    Sha3Done          = 9'b110011000, // sha3 mode, capture sha3 result, pulse done input
    Sha3Quiesce       = 9'b111001101, // sha3 mode, goto alert state or continuous check mode
    AlertState        = 9'b111111011, // if some alert condition occurs, pulse an alert indication
    AlertHang         = 9'b101011100, // after pulsing alert signal, hang here until sw handles
    Error             = 9'b100111101  // illegal state reached and hang
  } state_e;

endpackage
