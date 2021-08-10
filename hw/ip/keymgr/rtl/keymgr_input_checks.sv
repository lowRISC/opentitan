// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager input checks
// Checks input data for errors

`include "prim_assert.sv"

// We should also check for input validity
module keymgr_input_checks import keymgr_pkg::*; #(
  parameter bit KmacEnMasking = 1'b1
) (
  input rom_ctrl_pkg::keymgr_data_t rom_digest_i,
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
  output logic key_vld_o,
  output logic rom_digest_vld_o
);

  logic [31:0] cur_max_key_version;
  assign cur_max_key_version = max_key_versions_i[stage_sel_i];

  // key version must be smaller than or equal to max version
  assign key_version_vld_o = key_version_i <= cur_max_key_version;

  // general data check
  logic [MaxWidth-1:0] creator_seed_padded, owner_seed_padded, devid_padded, health_state_padded;

  prim_msb_extend #(
    .InWidth(KeyWidth),
    .OutWidth(MaxWidth)
  ) u_creator_seed (
    .in_i(creator_seed_i),
    .out_o(creator_seed_padded)
  );

  prim_msb_extend #(
    .InWidth(KeyWidth),
    .OutWidth(MaxWidth)
  ) u_owner_seed (
    .in_i(owner_seed_i),
    .out_o(owner_seed_padded)
  );

  prim_msb_extend #(
    .InWidth(DevIdWidth),
    .OutWidth(MaxWidth)
  ) u_devid (
    .in_i(devid_i),
    .out_o(devid_padded)
  );

  prim_msb_extend #(
    .InWidth(HealthStateWidth),
    .OutWidth(MaxWidth)
  ) u_health_state (
    .in_i(health_state_i),
    .out_o(health_state_padded)
  );

  assign creator_seed_vld_o = valid_chk(creator_seed_padded);
  assign owner_seed_vld_o = valid_chk(owner_seed_padded);
  assign devid_vld_o = valid_chk(devid_padded);
  assign health_state_vld_o = valid_chk(health_state_padded);

  // key check
  logic unused_key_vld;
  assign unused_key_vld = key_i.valid;

  localparam int KeyShares = KmacEnMasking ? Shares : 1;
  logic [KeyShares-1:0][MaxWidth-1:0] key_padded;
  logic [KeyShares-1:0] key_chk;

  for (genvar i = 0; i < KeyShares; i++) begin : gen_key_chk
    prim_msb_extend #(
      .InWidth(KeyWidth),
      .OutWidth(MaxWidth)
    ) u_key_pad (
      .in_i(key_i.key[i]),
      .out_o(key_padded[i])
    );

    assign key_chk[i] = valid_chk(key_padded[i]);
  end

  assign key_vld_o = &key_chk;

  // rom digest check
  assign rom_digest_vld_o = rom_digest_i.valid &
                            valid_chk(MaxWidth'(rom_digest_i.data));

  // checks for all 0's or all 1's of value
  function automatic logic valid_chk (logic [MaxWidth-1:0] value);

    return |value & ~&value;

  endfunction // valid_chk


endmodule // keymgr_input_checks
