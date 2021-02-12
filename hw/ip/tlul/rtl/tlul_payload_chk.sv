// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Tile-Link UL payload checker
 */

module tlul_payload_chk import tlul_pkg::*; (
  // TL-UL interface
  input  tl_h2d_t tl_i,

  // error output
  output logic err_o
);

  logic [1:0] err;
  tl_h2d_cmd_chk_t cmd;
  assign cmd = extract_h2d_cmd_chk(tl_i);

  prim_secded_64_57_dec u_chk (
    .in({tl_i.a_user.chk_cmd, H2DCmdMaxWidth'(cmd)}),
    .d_o(),
    .syndrome_o(),
    .err_o(err)
  );

  // TODO: The chk_en qualification here should be removed long term under a
  // compile time option.
  assign err_o = (tl_i.a_user.chk_en == CheckDis) ? 1'b0 : |err;

  logic unused_tl;
  assign unused_tl = |tl_i;

  `ASSERT_INIT(PayLoadWidthCheck, $bits(tl_h2d_cmd_chk_t) <= H2DCmdMaxWidth)

endmodule // tlul_payload_chk
