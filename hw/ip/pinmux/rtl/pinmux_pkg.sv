// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pinmux_pkg;

  // Wakeup Detector Modes
  typedef enum logic [2:0] {
    Posedge   = 3'b000,
    Negedge   = 3'b001,
    Edge      = 3'b010,
    HighTimed = 3'b011,
    LowTimed  = 3'b100
  } wkup_mode_e;

  // DFT Test Mode straps
  parameter int NDFTStraps  = 2;
  // Strap sampling is only supported on MIOs at the moment
  parameter int DftStrapPos [NDFTStraps] = '{3, 2};

  // Interface with LC controller
  typedef struct packed {
    logic                  valid;
    logic [NDFTStraps-1:0] straps;
  } dft_strap_test_req_t;

  // Life cycle DFT straps for TAP select
  parameter int NTapStraps  = 2;
  // Strap sampling is only supported on MIOs at the moment
  parameter int TapStrapPos [NTapStraps] = '{1, 0};

endpackage : pinmux_pkg
