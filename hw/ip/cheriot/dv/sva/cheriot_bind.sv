// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module cheriot_bind;

  bind cheriot tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device_regs (
    .clk_i,
    .rst_ni,
    .h2d  (regs_tl_d_i),
    .d2h  (regs_tl_d_o)
  );

  bind cheriot cheriot_regs_csr_assert_fpv cheriot_regs_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (regs_tl_d_i),
    .d2h    (regs_tl_d_o)
  );

endmodule
