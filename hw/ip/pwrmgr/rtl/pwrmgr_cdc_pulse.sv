// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager module to find slow clock edges
//

`include "prim_assert.sv"

module pwrmgr_cdc_pulse (
  input clk_slow_i,
  input clk_i,
  input rst_ni,
  input start_i,
  input stop_i,
  output logic pulse_o
);

  logic clk_slow_q;
  logic clk_slow_q2;
  logic toggle;
  logic valid;

  prim_flop_2sync # (
    .Width(1)
  ) i_sync (
    .clk_i,
    .rst_ni,
    .d(clk_slow_i),
    .q(clk_slow_q)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      clk_slow_q2 <= 1'b0;
    end else begin
      clk_slow_q2 <= clk_slow_q;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid <= 1'b0;
    end else if (valid & stop_i) begin
      valid <= 1'b0;
    end else if (!valid && toggle && start_i) begin
      valid <= 1'b1;
    end
  end

  assign toggle = clk_slow_q2 ^ clk_slow_q;
  assign pulse_o = valid & toggle;




endmodule // pwrmgr
