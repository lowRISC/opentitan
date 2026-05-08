// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This module is used to wrap different prim_flop variants to allow selecting the desired
// variant on a per-case basis using a compile-time parameter. This is particularly useful for
// building deeply pipelined masked circuits. If constructed properly, it is sufficient to only
// enable/disable the very first pipeline stage in such designs. The later pipeline stages can
// only update in subsequent clock cycles anyway, meaning they don't need an explicit enable
// signal. This allows replacing the prim_flop_en with a regular prim_flop without multiplexer cell
// on the input, which helps the reducing area for the later register stages by roughly 20%.

`include "prim_assert.sv"

module prim_flop_x #(
  parameter int               Width      = 1,
  parameter logic [Width-1:0] ResetValue = '0,
  parameter bit               PrimFlopEn = 1,
  parameter bit               EnSecBuf   = 0  // Ignored unless PrimFlopEn == 1.
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             en_i,
  input  logic [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  if (PrimFlopEn) begin : gen_prim_flop_en
    // Instantiate a prim_flop_en primitive.
    prim_flop_en #(
      .Width(Width),
      .EnSecBuf(EnSecBuf),
      .ResetValue(ResetValue)
    ) u_prim_flop (
      .clk_i,
      .rst_ni,
      .en_i,
      .d_i,
      .q_o
    );

  end else begin : gen_prim_flop
    // Instantiate a regular prim_flop primitive without enable input.
    prim_flop #(
      .Width(Width),
      .ResetValue(ResetValue)
    ) u_prim_flop (
      .clk_i,
      .rst_ni,
      .d_i,
      .q_o
    );

    // Tie-off the unused enable signal and EnSecBuf parameter.
    logic unused_en;
    assign unused_en = EnSecBuf ? ~en_i : en_i;
  end

endmodule
