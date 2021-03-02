// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Tile-Link UL response integrity check
 */

module tlul_rsp_intg_chk import tlul_pkg::*; (
  // TL-UL interface
  input  tl_d2h_t tl_i,

  // error output
  output logic err_o
);

  logic [1:0] err;
  tl_d2h_rsp_intg_t rsp;
  assign rsp = extract_d2h_rsp_intg(tl_i);

  prim_secded_64_57_dec u_chk (
    .in({tl_i.d_user.rsp_intg, D2HRspMaxWidth'(rsp)}),
    .d_o(),
    .syndrome_o(),
    .err_o(err)
  );

  assign err_o = |err;

  logic unused_tl;
  assign unused_tl = |tl_i;

  `ASSERT_INIT(PayLoadWidthCheck, $bits(tl_d2h_rsp_intg_t) <= D2HRspMaxWidth)

endmodule // tlul_rsp_intg_chk
