// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Tile-Link UL response integrity check
 */

module tlul_rsp_intg_chk import tlul_pkg::*; #(
  parameter bit EnableRspDataIntgCheck = 0
) (
  // TL-UL interface
  input  tl_d2h_t tl_i,

  // error output
  output logic err_o
);

  logic [1:0] rsp_err;
  tl_d2h_rsp_intg_t rsp;
  assign rsp = extract_d2h_rsp_intg(tl_i);

  prim_secded_inv_64_57_dec u_chk (
    .data_i({tl_i.d_user.rsp_intg, D2HRspMaxWidth'(rsp)}),
    .data_o(),
    .syndrome_o(),
    .err_o(rsp_err)
  );

  logic rsp_data_err;
  if (EnableRspDataIntgCheck) begin : gen_rsp_data_intg_check
    tlul_data_integ_dec u_tlul_data_integ_dec (
      .data_intg_i({tl_i.d_user.data_intg, DataMaxWidth'(tl_i.d_data)}),
      .data_err_o(rsp_data_err)
    );
  end else begin : gen_no_rsp_data_intg_check
    assign rsp_data_err = 1'b0;
  end

  // error is not permanently latched as rsp_intg_chk is typically
  // used near the host.
  // if the error is permanent, it would imply the host could forever
  // receive bus errors and lose all ability to debug.
  // It should be up to the host to determine the permanence of this error.
  assign err_o = tl_i.d_valid & (|rsp_err | rsp_data_err);

  logic unused_tl;
  assign unused_tl = |tl_i;

  `ASSERT_INIT(PayLoadWidthCheck, $bits(tl_d2h_rsp_intg_t) <= D2HRspMaxWidth)

endmodule // tlul_rsp_intg_chk
