// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This contains SVA assertions for clock gating output to alert_handler.
// - cg_en corresponds to clock gating enabled, which means the clock is gated,
//   thus inactive.
// - ip_clk_en and sw_clk_en have the opposite polarity: when they are active
//   the clock is enabled.
interface clkmgr_cg_en_sva_if
  import prim_mubi_pkg::*;
(
  input logic clk,
  input logic rst_n,
  input logic ip_clk_en,
  input logic sw_clk_en,
  input prim_mubi_pkg::mubi4_t scanmode,
  input logic cg_en
);

  bit   disable_sva;

  logic clk_enable;
  always_comb clk_enable = ip_clk_en && sw_clk_en;

  `ASSERT(CgEnOn_A, $fell(clk_enable) |=> ##[0:2] clk_enable || cg_en, clk,
          !rst_n || scanmode == prim_mubi_pkg::MuBi4True || disable_sva)
  `ASSERT(CgEnOff_A, $rose(clk_enable) |=> ##[0:2] !clk_enable || !cg_en, clk,
          !rst_n || scanmode == prim_mubi_pkg::MuBi4True || disable_sva)
endinterface
