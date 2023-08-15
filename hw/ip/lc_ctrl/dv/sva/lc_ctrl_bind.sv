// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module lc_ctrl_bind;

  bind lc_ctrl tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device_regs (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  bind lc_ctrl tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device_dmi (
    .clk_i,
    .rst_ni,
    .h2d  (dmi_tl_h2d_i),
    .d2h  (dmi_tl_d2h_o)
  );

  bind lc_ctrl lc_ctrl_csr_assert_fpv lc_ctrl_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o)
  );

endmodule
