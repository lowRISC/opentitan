// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module sram2tlul_bind;

  bind sram2tlul tlul_assert tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d    (tl_o),
    .d2h    (tl_i)
  );

endmodule
