# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file

# W_G_CLK_GLITCH
set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression             \
  {(GatedClockInput=~"top_earlgrey.u_pinmux_aon.*invert") && \
  (GatedClock=~ "top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.*req.tck")} -comment {W_G_CLK_GLITCH issues in JTAG}

set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression             \
  {(GatedClockInput=~"top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.*q_o*") && \
  (GatedClock=~ "top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.*req.tck")} -comment {W_G_CLK_GLITCH issues in JTAG}

set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression             \
  {(GatedClockInput=~"top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.tap_strap_q*") && \
  (GatedClock=~ "top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.*req.tck")} -comment {W_G_CLK_GLITCH issues in JTAG}

set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression             \
  {(GatedClockInput=~"top_earlgrey.u_pinmux_aon.*invert") && \
  (GatedClock=~ "top_earlgrey.u_rv_dm.jtag_in_int.tck")} -comment {W_G_CLK_GLITCH issues in JTAG}

set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression             \
  {(GatedClockInput=~"top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.*q_o*") && \
  (GatedClock=~ "top_earlgrey.u_rv_dm.jtag_in_int.tck")} -comment {W_G_CLK_GLITCH issues in JTAG}

set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression             \
  {(GatedClockInput=~"top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.tap_strap_q*") && \
  (GatedClock=~ "top_earlgrey.u_rv_dm.jtag_in_int.tck")} -comment {W_G_CLK_GLITCH issues in JTAG}

set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression             \
  {(GatedClockInput=~"IO*") && \
  (GatedClock=~ "u_ast.u_ast_clks_byp.u_clk_src*_sel.clk_o")} -comment {W_G_CLK_GLITCH issues in AST}

set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression             \
  {(GatedClockInput=~"u_ast.u_ast_clks_byp.u_clk_src*_sel.clk_ext_*") && \
  (GatedClock=~ "u_ast.u_ast_clks_byp.u_clk_src*_sel.clk_o")} -comment {W_G_CLK_GLITCH issues in AST}

set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression             \
  {(GatedClockInput=~"u_ast.*.u_impl_generic.q_o*") && \
  (GatedClock=~ "u_ast.u_ast_clks_byp.u_clk_src*_sel.clk_o")} -comment {W_G_CLK_GLITCH issues in AST}

set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression             \
  {(GatedClockInput=~"u_ast.*.*h_o*") && \
  (GatedClock=~ "u_ast.u_*_clk.u_*_osc.u_clk_ckgt.gen_generic.u_impl_generic.clk_o*")} -comment {W_G_CLK_GLITCH issues in AST}

set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression {(GatedClock=~ "top_earlgrey.u_clkmgr_aon.*.gen_generic.u_impl_generic.clk_o*")} -comment {W_G_CLK_GLITCH issues caused by AST and PAD}
set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression {(GatedClock=~ "top_earlgrey.u_clkmgr_aon.*.gen_generic.u_impl_generic.clk_o*")} -comment {W_G_CLK_GLITCH issues caused by AST and PAD}
set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression {(GatedClock=~ "top_earlgrey.u_lc_ctrl.*.gen_generic.u_impl_generic.clk_o*")} -comment {W_G_CLK_GLITCH issues caused by AST and PAD}
set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression {(GatedClock=~ "top_earlgrey.u_rv_core_ibex.*.gen_generic.u_impl_generic.clk_o*")} -comment {W_G_CLK_GLITCH issues caused by AST and PAD}
set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression {(GatedClock=~ "top_earlgrey.u_spi_device.*.gen_generic.u_impl_generic.clk_o*")} -comment {W_G_CLK_GLITCH issues caused by AST and PAD}
set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression {(GatedClock=~ "u_ast.clk_src*_o*")} -comment {W_G_CLK_GLITCH issues caused by AST and PAD}
set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression {(GatedClock=~ "top_earlgrey.u_rv_dm.jtag_in_int.tck*")} -comment {W_G_CLK_GLITCH issues caused by AST and PAD}
set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived} -expression {(GatedClock=~ "u_padring.gen_*io_pads*.u_*io_pad.gen_generic.u_impl_generic.in_o*")} -comment {W_G_CLK_GLITCH issues in PAD logic}
set_rule_status -rule {W_G_CLK_GLITCH} -expression {(GatedClock == "top_earlgrey.u_rv_dm.dap.i_dmi_jtag_tap.i_tck_inv.gen_generic.u_impl_generic.gen_scan.i_dft_tck_mux.gen_generic.u_impl_generic.clk_o") && (GlitchType == "ASYNC_INPUT")} -status {Waived} -comment {W_G_CLK_GLITCH issues in clkmux library. We created another clock mux to avoid any potential glitch}
set_rule_status -rule {W_G_CLK_GLITCH} -expression {(GatedClock == "top_earlgrey.u_rv_dm.u_prim_clock_mux2.gen_generic.u_impl_generic.clk_o") && (GlitchType == "ASYNC_INPUT")} -status {Waived} -comment {W_G_CLK_GLITCH issues in clkmux library. We created another clock mux to avoid any potential glitch}
