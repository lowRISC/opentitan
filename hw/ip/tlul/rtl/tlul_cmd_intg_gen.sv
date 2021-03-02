// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Tile-Link UL command integrity generator
 */

module tlul_cmd_intg_gen import tlul_pkg::*; (
  // TL-UL interface
  input  tl_h2d_t tl_i,
  output tl_h2d_t tl_o
);

  tl_h2d_cmd_intg_t cmd;
  assign cmd = extract_h2d_cmd_intg(tl_i);
  logic [H2DCmdMaxWidth-1:0] unused_cmd_payload;

  logic [H2DCmdIntgWidth-1:0] cmd_intg;
  prim_secded_64_57_enc u_cmd_gen (
    .in(H2DCmdMaxWidth'(cmd)),
    .out({cmd_intg, unused_cmd_payload})
  );

  always_comb begin
    tl_o = tl_i;
    tl_o.a_user.cmd_intg = cmd_intg;
  end

  logic unused_tl;
  assign unused_tl = ^tl_i;

  `ASSERT_INIT(PayMaxWidthCheck_A, $bits(tl_h2d_cmd_intg_t) <= H2DCmdMaxWidth)

endmodule // tlul_rsp_intg_gen
