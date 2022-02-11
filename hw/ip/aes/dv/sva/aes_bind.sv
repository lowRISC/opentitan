// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module aes_bind;

  bind aes tlul_assert #(
    .EndpointType("Device")
  )  tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  bind aes aes_csr_assert_fpv aes_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o)
  );

  bind aes aes_idle_check idle_check (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .reg2hw   (reg2hw),
    .idle_i   (idle_o)
   );


endmodule
