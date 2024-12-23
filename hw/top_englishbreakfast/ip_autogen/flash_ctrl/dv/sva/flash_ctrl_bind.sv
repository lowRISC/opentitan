// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module flash_ctrl_bind;

  bind flash_ctrl tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (core_tl_i),
    .d2h  (core_tl_o)
  );

  bind flash_ctrl flash_ctrl_core_csr_assert_fpv flash_ctrl_core_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (core_tl_i),
    .d2h    (core_tl_o)
  );

endmodule
