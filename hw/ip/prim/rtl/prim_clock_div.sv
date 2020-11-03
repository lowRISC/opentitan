// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_clock_div #(
  parameter int Divisor = 2,
  parameter logic ResetValue = 0
) (
  input clk_i,
  input rst_ni,
  input test_en_i,
  output logic clk_o
);


  logic clk_int;

  if (Divisor == 2) begin : gen_div2
    logic q_p, q_n;

    prim_flop # (
      .Width(1),
      .ResetValue(ResetValue)
    ) u_div2 (
      .clk_i,
      .rst_ni,
      .d_i(q_n),
      .q_o(q_p)
    );

    prim_clock_inv # (
      .HasScanMode(1'b0)
    ) u_inv (
      .clk_i(q_p),
      .scanmode_i('0),
      .clk_no(q_n)
    );

    assign clk_int = q_p;

  end else begin : gen_div
    // Only even divide is supported at the moment
    // For odd divide we need to introduce more parameters to control duty cycle
    `ASSERT_INIT(DivEven_A, (Divisor % 2) == 0)

    localparam int ToggleCnt = Divisor / 2;
    localparam int CntWidth = $clog2(ToggleCnt);
    logic [CntWidth-1:0] cnt;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        cnt <= '0;
        clk_int <= ResetValue;
      end else if (cnt == ToggleCnt-1) begin
        cnt <= '0;
        clk_int <= ~clk_o;
      end else begin
        cnt <= cnt + 1'b1;
      end
    end
  end

  // when in scanmode, bypass the dividers completely
  // also anchor point for constraints
  logic clk_muxed;

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_clk_mux (
    .clk0_i(clk_int),
    .clk1_i(clk_i),
    .sel_i(test_en_i),
    .clk_o(clk_muxed)
  );

  // anchor point for constraints
  prim_clock_buf u_clk_div_buf (
    .clk_i(clk_muxed),
    .clk_o
  );

endmodule
