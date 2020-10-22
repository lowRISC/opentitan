// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager input checks
// Checks input data for errors

`include "prim_assert.sv"

// We should also check for input validity
module keymgr_input_checks import keymgr_pkg::*;(
  input [2**StageWidth-1:0][31:0] max_key_versions_i,
  input keymgr_stage_e stage_sel_i,
  input [31:0] key_version_i,
  output logic key_version_good_o
);

  logic [31:0] cur_max_key_version;
  assign cur_max_key_version = max_key_versions_i[stage_sel_i];

  // key version must be smaller than or equal to max version
  assign key_version_good_o = key_version_i <= cur_max_key_version;



endmodule // keymgr_input_checks
