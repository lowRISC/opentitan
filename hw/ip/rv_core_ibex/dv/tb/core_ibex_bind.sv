// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module core_ibex_bind;

  bind rv_core_ibex tlul_assert tlul_assert_device_instr (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i_o),
    .d2h  (tl_i_i)
  );

  bind rv_core_ibex tlul_assert tlul_assert_device_data (
    .clk_i,
    .rst_ni,
    .h2d  (tl_d_o),
    .d2h  (tl_d_i)
  );

endmodule
