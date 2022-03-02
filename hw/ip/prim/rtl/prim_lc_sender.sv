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
  // This flops the output if set to 1.
  // In special cases where the sender is in the same clock domain as the receiver,
  // this can be set to 0. However, it is recommended to leave this at 1.
  parameter bit AsyncOn = 1,
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

  if (AsyncOn) begin : gen_flops
    prim_sec_anchor_flop #(
      .Width(lc_ctrl_pkg::TxWidth),
      .ResetValue(lc_ctrl_pkg::TxWidth'(ResetValue))
    ) u_prim_flop (
      .clk_i,
      .rst_ni,
      .d_i   ( lc_en     ),
      .q_o   ( lc_en_out )
    );
  end else begin : gen_no_flops
    for (genvar k = 0; k < lc_ctrl_pkg::TxWidth; k++) begin : gen_bits
      prim_sec_anchor_buf u_prim_buf (
        .in_i(lc_en[k]),
        .out_o(lc_en_out[k])
      );
    end

    // This unused companion logic helps remove lint errors
    // for modules where clock and reset are used for assertions only
    // or nothing at all.
    // This logic will be removed for sythesis since it is unloaded.
    lc_ctrl_pkg::lc_tx_t unused_logic;
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
         unused_logic <= lc_ctrl_pkg::Off;
      end else begin
         unused_logic <= lc_en_i;
      end
    end
  end

  assign lc_en_o = lc_ctrl_pkg::lc_tx_t'(lc_en_out);

endmodule : prim_lc_sender
