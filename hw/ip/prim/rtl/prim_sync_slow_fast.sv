// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Slow to fast clock synchronizer
// This module is designed to be used for efficient sampling of signals from a slow clock to a much
// faster clock.
//
// The data is captured into flops on the negative edge of the slow clock (when the data should be
// stable). Because the slow clock passes through a two-flop synchronizer, the ratio of clock speeds
// needs to be high to guarantee that the data will be stable when sampled.
//
// A ratio of at-least 10:1 in clock speeds is recommended.

module prim_sync_slow_fast #(
  parameter int unsigned Width = 32
) (
  input  logic             clk_slow_i,
  input  logic             clk_fast_i,
  input  logic             rst_fast_ni,
  input  logic [Width-1:0] wdata_i,    // Slow domain
  output logic [Width-1:0] rdata_o     // Fast domain
);

  logic             sync_clk_slow, sync_clk_slow_q;
  logic             wdata_en;
  logic [Width-1:0] wdata_q;

  // Synchronize the slow clock to the fast domain
  prim_flop_2sync #(.Width(1)) sync_slow_clk (
    .clk_i    (clk_fast_i),
    .rst_ni   (rst_fast_ni),
    .d_i      (clk_slow_i),
    .q_o      (sync_clk_slow));

  // Register the synchronized clk
  always_ff @(posedge clk_fast_i or negedge rst_fast_ni) begin
    if (!rst_fast_ni) begin
      sync_clk_slow_q <= 1'b0;
    end else begin
      sync_clk_slow_q <= sync_clk_slow;
    end
  end

  // Find the negative edge of the synchronized slow clk
  assign wdata_en = sync_clk_slow_q & !sync_clk_slow;

  // Sample the slow data on the negative edge
  always_ff @(posedge clk_fast_i or negedge rst_fast_ni) begin
    if (!rst_fast_ni) begin
      wdata_q <= '0;
    end else if (wdata_en) begin
      wdata_q <= wdata_i;
    end
  end

  assign rdata_o = wdata_q;

endmodule
