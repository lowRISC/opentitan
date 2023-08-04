// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module lc_ctrl_v1_bind;

  bind lc_ctrl_v1 tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  bind lc_ctrl_v1 lc_ctrl_v1_csr_assert_fpv lc_ctrl_v1_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o)
  );

endmodule
