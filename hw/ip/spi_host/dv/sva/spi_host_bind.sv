// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module spi_host_bind;

  bind spi_host tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  bind spi_host spi_host_csr_assert_fpv spi_host_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o)
  );

  bind spi_host spi_host_data_stable_sva spi_host_data_stable_assert (
    .rst_ni,
    .cio_sck_o,
    .cio_csb_o,
    .cio_sd_i,
    .cio_sd_en_o,
    .configopts(reg2hw.configopts),
    .passthrough_i
  );

endmodule
