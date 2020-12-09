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
  input hw_key_req_t key_i,
  input [31:0] key_version_i,
  input [KeyWidth-1:0] creator_seed_i,
  input [KeyWidth-1:0] owner_seed_i,
  input [DevIdWidth-1:0] devid_i,
  input [HealthStateWidth-1:0] health_state_i,
  output logic creator_seed_vld_o,
  output logic owner_seed_vld_o,
  output logic devid_vld_o,
  output logic health_state_vld_o,
  output logic key_version_vld_o,
  output logic key_vld_o
);

  logic [31:0] cur_max_key_version;
  assign cur_max_key_version = max_key_versions_i[stage_sel_i];

  // key version must be smaller than or equal to max version
  assign key_version_vld_o = key_version_i <= cur_max_key_version;

  // general data check
  assign creator_seed_vld_o = valid_chk(MaxWidth'(creator_seed_i));
  assign owner_seed_vld_o = valid_chk(MaxWidth'(owner_seed_i));
  assign devid_vld_o = valid_chk(MaxWidth'(devid_i));
  assign health_state_vld_o = valid_chk(MaxWidth'(health_state_i));

  // key check
  logic unused_key_vld;
  assign unused_key_vld = key_i.valid;
  assign key_vld_o = valid_chk(MaxWidth'(key_i.key_share0)) &
                     valid_chk(MaxWidth'(key_i.key_share1));

  // checks for all 0's or all 1's of value
  function automatic logic valid_chk (logic [MaxWidth-1:0] value);

    return |value & ~&value;

  endfunction // valid_chk


endmodule // keymgr_input_checks
