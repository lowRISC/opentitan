// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module clkmgr_bind;

  bind clkmgr tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));

  bind clkmgr clkmgr_csr_assert_fpv clkmgr_csr_assert (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));

  bind clkmgr clkmgr_pwrmgr_sva_if clkmgr_pwrmgr_sva_if (
    .clk_i, .rst_ni, .ip_clk_en(pwr_i.ip_clk_en), .clk_status(pwr_o.clk_status), .idle(idle_i)
  );
endmodule
