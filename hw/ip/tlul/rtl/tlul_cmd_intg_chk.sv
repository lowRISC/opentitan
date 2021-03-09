// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Tile-Link UL command integrity check
 */

module tlul_cmd_intg_chk import tlul_pkg::*; (
  // TL-UL interface
  input  tl_h2d_t tl_i,

  // error output
  output logic err_o
);

  logic [1:0] err;
  tl_h2d_cmd_intg_t cmd;
  assign cmd = extract_h2d_cmd_intg(tl_i);

  prim_secded_64_57_dec u_chk (
    .in({tl_i.a_user.cmd_intg, H2DCmdMaxWidth'(cmd)}),
    .d_o(),
    .syndrome_o(),
    .err_o(err)
  );

  // error output is transactional, it is up to the instantiating module
  // to determine if a permanent latch is feasible
  assign err_o = tl_i.a_valid & |err;

  logic unused_tl;
  assign unused_tl = |tl_i;

  `ASSERT_INIT(PayLoadWidthCheck, $bits(tl_h2d_cmd_intg_t) <= H2DCmdMaxWidth)

endmodule // tlul_payload_chk
