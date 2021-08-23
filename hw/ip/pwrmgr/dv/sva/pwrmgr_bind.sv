// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module pwrmgr_bind;

  bind pwrmgr tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));

  bind pwrmgr pwrmgr_csr_assert_fpv pwrmgr_csr_assert (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));

  // Clock control assertions.
  bind pwrmgr pwrmgr_clock_enables_sva_if pwrmgr_clock_enables_sva_if (
    .clk_i(clk_slow_i),
    .rst_ni(rst_slow_ni),
    .state(i_slow_fsm.state_q),
    // The synchronized control CSR bits.
    .main_pd_ni(slow_main_pd_n),
    .core_clk_en_i(slow_core_clk_en),
    .io_clk_en_i(slow_io_clk_en),
    .usb_clk_en_lp_i(slow_usb_clk_en_lp),
    .usb_clk_en_active_i(slow_usb_clk_en_active),
    // The main power control.
    .main_pd_n(pwr_ast_o.main_pd_n),
    // The output enables.
    .core_clk_en(pwr_ast_o.core_clk_en),
    .io_clk_en(pwr_ast_o.io_clk_en),
    .usb_clk_en(pwr_ast_o.usb_clk_en)
  );

  bind pwrmgr pwrmgr_ast_sva_if pwrmgr_ast_sva_if (
    .clk_slow_i,
    .rst_slow_ni,
    // The pwrmgr outputs.
    .pwr_ast_o,
    // The pwrmgr input.
    .pwr_ast_i
  );

  bind pwrmgr pwrmgr_rstmgr_sva_if pwrmgr_rstmgr_sva_if (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    // The outputs from pwrmgr.
    .rst_lc_req(pwr_rst_o.rst_lc_req),
    .rst_sys_req(pwr_rst_o.rst_sys_req),
    .ndm_sys_req(1'b0),
    .reset_cause(pwrmgr_pkg::ResetNone),
    // The inputs from rstmgr.
    .rst_lc_src_n(pwr_rst_i.rst_lc_src_n),
    .rst_sys_src_n(pwr_rst_i.rst_sys_src_n)
  );

endmodule
