// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module padctrl_bind_fpv;

  bind padring padring_assert_fpv i_padring_assert_fpv (
    .*
  );

  bind padctrl padctrl_assert_fpv i_padctrl_assert_fpv (
    .*
  );

  bind padctrl tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  bind padctrl padctrl_csr_assert_fpv i_padctrl_csr_assert_fpv (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o),
    .reg2hw (reg2hw),
    .hw2reg (hw2reg)
  );
endmodule : padctrl_bind_fpv
