// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_bind;
`ifndef GATE_LEVEL
  bind top_earlgrey clk_ctrl_and_main_pd_sva_if clk_ctrl_and_main_pd_sva_if (
    .clk_slow_i(u_pwrmgr_aon.clk_slow_i),
    .rst_slow_ni(u_pwrmgr_aon.rst_slow_ni),
    .por_d0_ni(por_n_i[1]),
    .core_clk_en(u_pwrmgr_aon.pwr_ast_o.core_clk_en),
    .core_clk_val(u_pwrmgr_aon.pwr_ast_i.core_clk_val),
    .clk_core_i(u_clkmgr_aon.clk_main_i),
    .io_clk_en(u_pwrmgr_aon.pwr_ast_o.io_clk_en),
    .io_clk_val(u_pwrmgr_aon.pwr_ast_i.io_clk_val),
    .clk_io_i(u_clkmgr_aon.clk_io_i),
    .usb_clk_en(u_pwrmgr_aon.pwr_ast_o.usb_clk_en),
    .usb_clk_val(u_pwrmgr_aon.pwr_ast_i.usb_clk_val),
    .clk_usb_i(u_clkmgr_aon.clk_usb_i),
    .main_pd_n(u_pwrmgr_aon.pwr_ast_o.main_pd_n),
    .main_pok(u_pwrmgr_aon.pwr_ast_i.main_pok)
  );

  bind top_earlgrey pwrmgr_rstreqs_sva_if pwrmgr_rstreqs_sva_if (
    .clk_i(u_pwrmgr_aon.clk_i),
    .rst_ni(u_pwrmgr_aon.rst_ni),
    .clk_slow_i(u_pwrmgr_aon.clk_slow_i),
    .rst_slow_ni(u_pwrmgr_aon.rst_slow_ni),
    // Input resets.
    .rstreqs_i(u_pwrmgr_aon.rstreqs_i),
    .reset_en(u_pwrmgr_aon.reg2hw.reset_en),
    .sw_rst_req_i(prim_mubi_pkg::mubi4_test_true_strict(u_pwrmgr_aon.sw_rst_req_i)),
    .main_rst_req_i(!u_pwrmgr_aon.rst_main_ni),
    .esc_rst_req_i(u_pwrmgr_aon.esc_rst_req_q),
    .ndm_rst_req_i(u_pwrmgr_aon.ndmreset_req_i),
    // The outputs from pwrmgr.
    .rstreqs(u_pwrmgr_aon.pwr_rst_o.rstreqs),
    .main_pd_n(u_pwrmgr_aon.pwr_ast_o.main_pd_n),
    .reset_cause(u_pwrmgr_aon.pwr_rst_o.reset_cause)
  );
`endif

endmodule
