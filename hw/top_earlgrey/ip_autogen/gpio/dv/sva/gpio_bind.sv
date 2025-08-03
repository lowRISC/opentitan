// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module gpio_bind;

  bind gpio tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  bind gpio gpio_csr_assert_fpv gpio_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o)
  );

  bind gpio gpio_strap_check #(.NUM_GPIOS($bits(cio_gpio_i)))
  gpio_strap_assert (
    .clk_i,
    .rst_ni,
    .strap_en_i,
    .strap_valid(sampled_straps_o.valid),
    .strap_data(sampled_straps_o.data),
    .gpio_i(cio_gpio_i)
  );

endmodule
