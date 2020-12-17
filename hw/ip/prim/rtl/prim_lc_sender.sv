// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Multibit life cycle signal sender module.
//
// This module is combinational and instantiates a hand-picked buffer cell
// for each bit in the life cycle control signal such that tools do not
// optimize the multibit encoding.

`include "prim_assert.sv"

module prim_lc_sender (
  input  lc_ctrl_pkg::lc_tx_t lc_en_i,
  output lc_ctrl_pkg::lc_tx_t lc_en_o
);

  logic [lc_ctrl_pkg::TxWidth-1:0] lc_en, lc_en_out;
  assign lc_en = lc_ctrl_pkg::TxWidth'(lc_en_i);

  for (genvar k = 0; k < lc_ctrl_pkg::TxWidth; k++) begin : gen_bits
    prim_buf u_prim_buf (
      .in_i(lc_en[k]),
      .out_o(lc_en_out[k])
    );
  end

  assign lc_en_o = lc_ctrl_pkg::lc_tx_t'(lc_en_out);

endmodule : prim_lc_sender
