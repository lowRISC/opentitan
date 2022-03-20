// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module pwrmgr_bind;

  bind pwrmgr tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));

  // In top-level testbench, do not bind the csr_assert_fpv to reduce simulation time.
  `ifndef TOP_LEVEL_DV
  bind pwrmgr pwrmgr_csr_assert_fpv pwrmgr_csr_assert (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));
  `endif

  // Clock control assertions.
  bind pwrmgr pwrmgr_clock_enables_sva_if pwrmgr_clock_enables_sva_if (
    .clk_i(clk_slow_i),
    .rst_ni(rst_slow_ni),
    .fast_state(u_fsm.state_q),
    .slow_state(u_slow_fsm.state_q),
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

  bind pwrmgr clkmgr_pwrmgr_sva_if clkmgr_pwrmgr_sva_if (
    .clk_i,
    .rst_ni,
    .io_clk_en(pwr_clk_o.io_ip_clk_en),
    .io_status(pwr_clk_i.io_status),
    .main_clk_en(pwr_clk_o.main_ip_clk_en),
    .main_status(pwr_clk_i.main_status),
    .usb_clk_en(pwr_clk_o.usb_ip_clk_en),
    .usb_status(pwr_clk_i.usb_status)
  );

  bind pwrmgr pwrmgr_sec_cm_checker_assert pwrmgr_sec_cm_checker_assert (
    .clk_i,
    .rst_ni,
    .rom_intg_chk_dis(u_fsm.rom_intg_chk_dis),
    .lc_dft_en_i,
    .lc_hw_debug_en_i
  );
endmodule
