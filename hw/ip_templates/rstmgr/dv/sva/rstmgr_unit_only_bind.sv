// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This binds assertions that should not be bound at chip level.
module rstmgr_unit_only_bind;

  // In top-level testbench, do not bind the csr_assert_fpv to reduce simulation time.
  bind rstmgr rstmgr_csr_assert_fpv rstmgr_csr_assert (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));

  bind rstmgr pwrmgr_rstmgr_sva_if pwrmgr_rstmgr_sva_if (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clk_slow_i(clk_aon_i),
    .rst_slow_ni(&rst_por_aon_n),
    // These are actually used for checks.
    .rst_lc_req(pwr_i.rst_lc_req),
    .rst_sys_req(pwr_i.rst_sys_req),
    // The inputs from rstmgr.
    .rst_lc_src_n(pwr_o.rst_lc_src_n),
    .rst_sys_src_n(pwr_o.rst_sys_src_n)
  );

endmodule : rstmgr_unit_only_bind
