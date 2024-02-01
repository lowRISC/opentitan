// Copyright lowRISC contributors (OpenTitan project).
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

  bind i2c i2c_csr_assert_fpv i2c_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o)
  );

  bind i2c i2c_protocol_cov u_i2c_protocol_cov(
    .clk (clk_i),
    .rst_n (rst_ni),
    .scl (cio_scl_i),
    .sda (cio_sda_i),
    .intr_cmd_complete (intr_cmd_complete_o),
    .intr_tx_stretch   (intr_tx_stretch_o)
  );

endmodule
