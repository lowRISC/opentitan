// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pinmux_pkg;

  // Wakeup Detector Modes
  typedef enum logic [2:0] {
    Disabled  = 3'b000,
    Negedge   = 3'b001,
    Posedge   = 3'b010,
    Edge      = 3'b011,
    LowTimed  = 3'b100,
    HighTimed = 3'b101
  } wkup_mode_e;

  // Number of IO power OK signals
  parameter int NIOPokSignals = 2;

  typedef struct packed {
    logic [NIOPokSignals-1:0] domain;
  } io_pok_req_t;

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
  parameter int NLcStraps  = 2;
  // Strap sampling is only supported on MIOs at the moment
  parameter int LcStrapPos [NLcStraps] = '{1, 0};

  // Interface with LC controller
  typedef struct packed {
    logic sample_pulse;
  } lc_strap_req_t;

  typedef struct packed {
    logic                 valid;
    logic [NLcStraps-1:0] straps;
  } lc_strap_rsp_t;

endpackage : pinmux_pkg
