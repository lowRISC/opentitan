// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_flop #(
  parameter int               Width      = 1,
  parameter logic [Width-1:0] ResetValue = 0
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  logic [Width-1:0] qn;

  for (genvar idx = 0; idx < Width; idx++) begin : gen_bits
    if (ResetValue[idx] == 1'b0) begin : g_reset_low
      DFFASRHQNx1_ASAP7_75t_R u_size_only_flop_reset_low (
        .CLK   (clk_i),
        .RESETN(rst_ni),
        .D     (d_i[idx]),
        .SETN  (1'b1),
        .QN    (qn[idx])
      );
    end else begin : g_reset_high
      DFFASRHQNx1_ASAP7_75t_R u_size_only_flop_reset_high (
        .CLK   (clk_i),
        .RESETN(1'b1),
        .D     (d_i[idx]),
        .SETN  (rst_ni),
        .QN    (qn[idx])
      );
    end

    assign q_o[idx] = ~qn[idx];
  end

endmodule
