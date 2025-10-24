// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_flop_en #(
  parameter int               Width      = 1,
  parameter bit               EnSecBuf   = 0,
  parameter logic [Width-1:0] ResetValue = 0
) (
  input  logic             clk_i,
  input  logic             rst_ni,
  input  logic             en_i,
  input  logic [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  logic             en;
  logic [Width-1:0] d;
  logic [Width-1:0] qn;

  if (EnSecBuf) begin : gen_en_sec_buf
    BUFx2_ASAP7_75t_R u_size_only_sec_anchor_buf (
      .A(en_i),
      .Y(en)
    );
  end else begin : gen_en_no_sec_buf
    assign en = en_i;
  end

  // In ASAP7 the enable FF is built with a generic FF and a mux
  assign d = en ? d_i : ~qn;

  for (genvar idx = 0; idx < Width; idx++) begin : gen_bits

    if (ResetValue[idx] == 1'b0) begin : g_reset_low
      DFFASRHQNx1_ASAP7_75t_R u_size_only_flop_reset_low (
        .CLK   (clk_i),
        .RESETN(rst_ni),
        .D     (d[idx]),
        .SETN  (1'b1),
        .QN    (qn[idx])
      );
    end else begin : g_reset_high
      DFFASRHQNx1_ASAP7_75t_R u_size_only_flop_reset_high (
        .CLK   (clk_i),
        .RESETN(1'b1),
        .D     (d[idx]),
        .SETN  (rst_ni),
        .QN    (qn[idx])
      );
    end
    assign q_o[idx] = ~qn[idx];
  end

endmodule
