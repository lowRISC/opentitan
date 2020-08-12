// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module i2c_bind;

  bind i2c tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  import i2c_reg_pkg::*;
  bind i2c i2c_csr_assert_fpv i2c_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o),
    .reg2hw (reg2hw),
    .hw2reg (hw2reg)
  );

endmodule
