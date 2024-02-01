// Copyright lowRISC contributors (OpenTitan project).
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
  // This fires at negedges: if the gated clock is inactive its value is expected to be low,
  // and viceversa. The assertions pass if clk_enabled is not stable to avoid cycle accuracy, and
  // these gated clocks are expected to be changed infrequently.
  logic clk_enabled;
  always_comb clk_enabled = sw_clk_en && ip_clk_en || scanmode;

  `ASSERT(GateOpen_A,
          $rose(clk_enabled) |=> ##[0:3] !clk_enabled || $changed(clk_enabled) || gated_clk, !clk,
          !rst_n)
  `ASSERT(GateClose_A,
          $fell(clk_enabled) |=> ##[0:3] clk_enabled || $changed(clk_enabled) || !gated_clk, !clk,
          !rst_n)
endinterface
