// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Multibit life cycle signal sender module.
//
// This module is instantiates a hand-picked flop cell
// for each bit in the life cycle control signal such that tools do not
// optimize the multibit encoding.

`include "prim_assert.sv"

module prim_lc_sender #(
  // 0: reset value is lc_ctrl_pkg::Off
  // 1: reset value is lc_ctrl_pkg::On
  parameter bit ResetValueIsOn = 0
) (
  input                       clk_i,
  input                       rst_ni,
  input  lc_ctrl_pkg::lc_tx_t lc_en_i,
  output lc_ctrl_pkg::lc_tx_t lc_en_o
);

  localparam lc_ctrl_pkg::lc_tx_t ResetValue = (ResetValueIsOn) ? lc_ctrl_pkg::On :
                                                                  lc_ctrl_pkg::Off;

  logic [lc_ctrl_pkg::TxWidth-1:0] lc_en, lc_en_out;
  assign lc_en = lc_ctrl_pkg::TxWidth'(lc_en_i);

  prim_sec_anchor_flop #(
    .Width(lc_ctrl_pkg::TxWidth),
    .ResetValue(lc_ctrl_pkg::TxWidth'(ResetValue))
  ) u_prim_flop (
    .clk_i,
    .rst_ni,
    .d_i   ( lc_en     ),
    .q_o   ( lc_en_out )
  );

  assign lc_en_o = lc_ctrl_pkg::lc_tx_t'(lc_en_out);

endmodule : prim_lc_sender
