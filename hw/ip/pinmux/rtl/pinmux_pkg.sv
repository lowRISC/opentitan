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

  // Interface with LC controller
  parameter int NStraps  = 2;
  // Strap sampling is only supported on MIOs at the moment
  parameter int MioStrapPos [0:NStraps-1] = '{1, 0};

  typedef struct packed {
    logic sample_pulse;
  } lc_strap_req_t;

  parameter lc_strap_req_t LC_PINMUX_STRAP_REQ_DEFAULT = '{
    sample_pulse: 1'b0
  };

  typedef struct packed {
    logic               valid;
    logic [NStraps-1:0] straps;
  } lc_strap_rsp_t;

endpackage : pinmux_pkg
