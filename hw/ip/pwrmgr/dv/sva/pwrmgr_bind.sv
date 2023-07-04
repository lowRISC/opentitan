// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module pwrmgr_bind;
`ifndef GATE_LEVEL
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
    .usb_ip_clk_status_i(usb_ip_clk_status),
    // The main power control.
    .main_pd_n(pwr_ast_o.main_pd_n),
    // The output enables.
    .core_clk_en(pwr_ast_o.core_clk_en),
    .io_clk_en(pwr_ast_o.io_clk_en),
    .usb_clk_en(pwr_ast_o.usb_clk_en)
  );

  bind pwrmgr pwrmgr_rstmgr_sva_if pwrmgr_rstmgr_sva_if (
    .clk_i,
    .rst_ni,
    .clk_slow_i,
    .rst_slow_ni,
    // The outputs from pwrmgr.
    .rst_lc_req(pwr_rst_o.rst_lc_req),
    .rst_sys_req(pwr_rst_o.rst_sys_req),
    // The inputs from rstmgr.
    .rst_lc_src_n(pwr_rst_i.rst_lc_src_n),
    .rst_sys_src_n(pwr_rst_i.rst_sys_src_n)
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
    .clk_lc_i,
    .rst_lc_ni,
    .clk_esc_i,
    .rst_esc_ni,
    .clk_slow_i,
    .rst_slow_ni,
    .rst_main_ni,
    .pwr_rst_o,
    .slow_esc_rst_req(slow_peri_reqs.rstreqs[3]),
    .slow_mp_rst_req(slow_peri_reqs.rstreqs[2]),
    .slow_fsm_invalid,
    .fast_fsm_invalid(u_fsm.u_state_regs.unused_err_o),
    .rom_intg_chk_dis(u_fsm.rom_intg_chk_dis),
    .rom_intg_chk_ok(prim_mubi_pkg::mubi4_and_hi(u_fsm.rom_intg_chk_done, u_fsm.rom_intg_chk_good)),
    .lc_dft_en_i(u_fsm.lc_hw_debug_en_i),
    .lc_hw_debug_en_i(u_fsm.lc_hw_debug_en_i),
    .main_pd_ni(u_slow_fsm.main_pd_ni),
    .rom_ctrl_done_i(u_fsm.rom_ctrl_done_i),
    .rom_ctrl_good_i(u_fsm.rom_ctrl_good_i)
  );
`endif
endmodule
