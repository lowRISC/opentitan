// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager module to find slow clock edges
// The clock is not used directly to avoid STA issues, instead a toggle
// pulse is used.

`include "prim_assert.sv"

module pwrmgr_cdc_pulse (
  input clk_slow_i,
  input clk_i,
  input rst_ni,
  input rst_slow_ni,
  input start_i,
  input stop_i,
  output logic pulse_o
);

  logic slow_toggle_pq, slow_toggle_nq;
  logic clk_slow_pq, clk_slow_nq;
  logic clk_slow_pq2, clk_slow_nq2;
  logic toggle;
  logic valid;

  // toggle pulse generated on positive edge
  always_ff @(posedge clk_slow_i or negedge rst_slow_ni) begin
    if (!rst_slow_ni) begin
      slow_toggle_pq <= 1'b0;
    end else begin
      slow_toggle_pq <= ~slow_toggle_pq;
    end
  end

  // toggle pulse generated on negative edge
  always_ff @(negedge clk_slow_i or negedge rst_slow_ni) begin
    if (!rst_slow_ni) begin
      slow_toggle_nq <= 1'b0;
    end else begin
      slow_toggle_nq <= ~slow_toggle_nq;
    end
  end


  prim_flop_2sync # (
    .Width(1)
  ) i_pos_sync (
    .clk_i,
    .rst_ni,
    .d_i(slow_toggle_pq),
    .q_o(clk_slow_pq)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_neg_sync (
    .clk_i,
    .rst_ni,
    .d_i(slow_toggle_nq),
    .q_o(clk_slow_nq)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      clk_slow_pq2 <= 1'b0;
      clk_slow_nq2 <= 1'b0;
    end else begin
      clk_slow_pq2 <= clk_slow_pq;
      clk_slow_nq2 <= clk_slow_nq;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid <= 1'b0;
    end else if (valid && stop_i) begin
      valid <= 1'b0;
    end else if (!valid && toggle && start_i) begin
      valid <= 1'b1;
    end
  end

  // toggle is found on either positive and negative edges of clk_slow_i
  assign toggle = clk_slow_pq2 ^ clk_slow_pq | clk_slow_nq2 ^ clk_slow_nq;
  assign pulse_o = valid & toggle;




endmodule // pwrmgr
