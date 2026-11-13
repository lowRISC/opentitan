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

  if (EnSecBuf) begin : gen_en_sec_buf
    (* keep *) sg13cmos5l_buf_2 u_sec_anchor_buf (
      .A(en_i),
      .X(en)
    );
  end else begin : gen_en_no_sec_buf
    assign en = en_i;
  end

  // In IHP130 the enable FF is built with a generic FF and a mux
  assign d = en ? d_i : q_o;

  for (genvar idx = 0; idx < Width; idx++) begin : gen_bits

    if (ResetValue[idx] == 1'b0) begin : g_reset_low
      sg13cmos5l_dfrbp_1 u_flop (
        .CLK    (clk_i),
        .D      (d[idx]),
        .RESET_B(rst_ni),
        .Q      (q_o[idx]),
        .Q_N    ()
      );
    end else begin : g_reset_high
      logic d_n;
      sg13cmos5l_inv_1 u_inv (
        .A(d[idx]),
        .Y(d_n)
      );
      sg13cmos5l_dfrbp_1 u_flop (
        .CLK    (clk_i),
        .D      (d_n),
        .RESET_B(rst_ni),
        .Q      (),
        .Q_N    (q_o[idx])
      );
    end
  end

endmodule
