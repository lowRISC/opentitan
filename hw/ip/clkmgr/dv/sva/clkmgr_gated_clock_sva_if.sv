// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This contains SVA assertions for gated clocks.
interface clkmgr_gated_clock_sva_if (
  input logic clk,
  input logic rst_n,
  input logic ip_clk_en,
  input logic sw_clk_en,
  input logic scanmode,
  input logic gated_clk
);
  // This fires at negedges, so check $past(clk*) as activity.
  logic gating;
  always_comb gating = sw_clk_en && ip_clk_en || scanmode;

  `ASSERT(GateOpen_A, $rose(gating) |-> ##[1:3] !gating || gated_clk, !clk, !rst_n)
  `ASSERT(GateClose_A, $fell(gating) |-> ##[1:3] gating || !gated_clk, !clk, !rst_n)
endinterface
