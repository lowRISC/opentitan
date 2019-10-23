// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tlul_adapter_sram_bind;

  bind tlul_adapter_sram tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_host (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o)
  );

endmodule
