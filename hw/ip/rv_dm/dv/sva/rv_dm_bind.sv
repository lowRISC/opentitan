// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module rv_dm_bind;

  bind rv_dm tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device_regs (
    .clk_i,
    .rst_ni,
    .h2d  (regs_tl_d_i),
    .d2h  (regs_tl_d_o)
  );

  bind rv_dm tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device_mem (
    .clk_i,
    .rst_ni,
    .h2d  (mem_tl_d_i),
    .d2h  (mem_tl_d_o)
  );

  bind rv_dm tlul_assert #(
    .EndpointType("Host")
  ) tlul_assert_host_sba (
    .clk_i,
    .rst_ni,
    .h2d  (sba_tl_h_o),
    .d2h  (sba_tl_h_i)
  );

  bind rv_dm rv_dm_regs_csr_assert_fpv rv_dm_regs_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (regs_tl_d_i),
    .d2h    (regs_tl_d_o)
  );

  // TODO: What about 'rv_dm_mem_csr_assert_fpv?

  bind rv_dm rv_dm_enable_checker enable_checker (
    .clk_i (clk_i),
    .rst_ni (rst_ni),
    .lc_hw_debug_en_i(lc_hw_debug_en_i),
    .lc_dft_en_i(lc_dft_en_i),
    .otp_dis_rv_dm_late_debug_i(otp_dis_rv_dm_late_debug_i),
    .debug_req_o_i(debug_req_o),
    .mem_tl_d_o_i(mem_tl_d_o),
    .sba_tl_h_o_i(sba_tl_h_o),

    .ndmreset_ack,
    .regs_reg2hw
  );

endmodule
