// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_bind;

  bind otbn tlul_assert #(
    .EndpointType("Device")
  ) tlul_checker (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .h2d    (tl_i),
    .d2h    (tl_o)
  );

  import otbn_reg_pkg::*;
  bind otbn otbn_csr_assert_fpv csr_checker (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .h2d    (tl_i),
    .d2h    (tl_o),
    .reg2hw (reg2hw),
    .hw2reg (hw2reg)
  );

endmodule
