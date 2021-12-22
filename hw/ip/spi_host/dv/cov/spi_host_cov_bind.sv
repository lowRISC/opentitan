// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds UART functional coverage interaface to the top level AES module.
module spi_host_cov_bind;

  bind spi_host spi_host_cov_if u_spi_cov_if (
    .clk_i           (clk_i)
  );

endmodule
