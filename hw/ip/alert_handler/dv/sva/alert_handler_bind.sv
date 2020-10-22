// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module alert_handler_bind;

  bind alert_handler tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  import alert_handler_reg_pkg::*;
  bind alert_handler alert_handler_csr_assert_fpv alert_handler_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o),
    .reg2hw (i_reg_wrap.reg2hw),
    .hw2reg (i_reg_wrap.hw2reg)
  );

endmodule
