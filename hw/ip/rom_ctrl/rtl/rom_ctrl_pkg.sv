// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

package rom_ctrl_pkg;

  parameter int AlertFatal = 0;

  typedef struct packed {
    logic done;
    logic good;
  } pwrmgr_data_t;

  typedef struct packed {
    logic [31:0] data;
    logic        valid;
    logic        last;
  } keymgr_data_t;

endpackage
