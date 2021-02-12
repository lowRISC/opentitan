// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Tile-Link UL payload checker generator
 */

module tlul_gen_payload_chk import tlul_pkg::*; (
  // TL-UL interface
  input  tl_d2h_t tl_i,
  output tl_d2h_t tl_o
);

  tl_d2h_rsp_chk_t rsp;
  logic [D2HRspMaxWidth-1:0] unused_payload;
  logic [D2HRspChkWidth-1:0] chk;
  assign rsp = extract_d2h_rsp_chk(tl_i);

  prim_secded_64_57_enc u_gen (
    .in(D2HRspMaxWidth'(rsp)),
    .out({chk, unused_payload})
  );

  always_comb begin
    tl_o = tl_i;
    if (tl_i.d_user.chk_en == CheckDis) begin
      tl_o.d_user.chk_en = CheckEn;
      tl_o.d_user.chk_rsp = chk;
    end
  end


  `ASSERT_INIT(PayLoadWidthCheck, $bits(tl_d2h_rsp_chk_t) <= D2HRspMaxWidth)

endmodule // tlul_payload_chk
