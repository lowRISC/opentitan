// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is split off from pwrmgr_bind so that we can instantiate that in chip top, but
// specialize the bind of pwrmgr_rstmgr_sva_if for top_earlgrey, which is needed in order
// to hook up ndm_sys_req because pwrmgr doesn't see it.
module pwrmgr_unit_bind;

  bind pwrmgr pwrmgr_rstmgr_sva_if pwrmgr_rstmgr_sva_if (
    .clk_i,
    .rst_ni,
    .clk_slow_i,
    .rst_slow_ni,
    // Input resets.
    .rstreqs_i(rstreqs_i),
    .reset_en(reg2hw.reset_en),
    .sw_rst_req_i(prim_mubi_pkg::mubi4_test_true_strict(sw_rst_req_i)),
    .main_rst_req_i(!rst_main_ni),
    .esc_rst_req_i(esc_rst_req_q),
    // The outputs from pwrmgr.
    .rst_lc_req(pwr_rst_o.rst_lc_req),
    .rst_sys_req(pwr_rst_o.rst_sys_req),
    .rstreqs(pwr_rst_o.rstreqs),
    .main_pd_n(pwr_ast_o.main_pd_n),
    .reset_cause(pwr_rst_o.reset_cause),
    // This goes directly to rstmgr and can trigger rst_sys_src_n.
    .ndm_sys_req(1'b0),
    // The inputs from rstmgr.
    .rst_lc_src_n(pwr_rst_i.rst_lc_src_n),
    .rst_sys_src_n(pwr_rst_i.rst_sys_src_n)
  );

  bind pwrmgr pwrmgr_ast_sva_if #(
    .CheckClocks(1'b0)
  ) pwrmgr_ast_sva_if (
    .clk_slow_i,
    .rst_slow_ni,
    // Leave clk_*_i inputs unconnected as they are not used by assertions in unit tests.
    // The pwrmgr outputs.
    .pwr_ast_o,
    // The pwrmgr input.
    .pwr_ast_i
  );

endmodule
