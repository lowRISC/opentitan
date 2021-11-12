// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

package rom_ctrl_pkg;

  parameter int AlertFatal = 0;

  typedef struct packed {
    prim_mubi_pkg::mubi4_t done;
    prim_mubi_pkg::mubi4_t good;
  } pwrmgr_data_t;

  parameter pwrmgr_data_t PWRMGR_DATA_DEFAULT = '{
    done: prim_mubi_pkg::MuBi4True,
    good: prim_mubi_pkg::MuBi4True
  };

  typedef struct packed {
    logic [255:0] data;
    logic         valid;
  } keymgr_data_t;

endpackage
