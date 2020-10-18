// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pattgen_ctrl_pkg;

  typedef struct packed {
    logic        enable;
    logic        polarity;
    logic [31:0] prediv;
    logic [63:0] data;
    logic [5:0]  len;
    logic [9:0]  reps;
  } pattgen_chan_ctrl_t;

endpackage : pattgen_ctrl_pkg
