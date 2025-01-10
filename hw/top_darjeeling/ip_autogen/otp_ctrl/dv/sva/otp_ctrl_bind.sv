// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otp_ctrl_bind;

  bind otp_ctrl tlul_assert #(
    .EndpointType("Device")
  ) core_tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (core_tl_i),
    .d2h  (core_tl_o)
  );

  bind otp_ctrl tlul_assert #(
    .EndpointType("Device")
  ) prim_tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (prim_tl_i),
    .d2h  (prim_tl_o)
  );

  bind otp_ctrl otp_ctrl_core_csr_assert_fpv otp_ctrl_core_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (core_tl_i),
    .d2h    (core_tl_o)
  );

endmodule
