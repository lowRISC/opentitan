// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module rv_plic_bind;
  bind rv_plic rv_plic_assert rv_plic_assert (
    .clk_i,
    .rst_ni,
    .intr_src_i,
    .irq_o,
    .irq_id_o,
    .msip_o
  );
  bind rv_plic tlul_assert tlul_assert_host(
    .clk_i,
    .rst_ni,
    .h2d(tl_i),
    .d2h(tl_o)
  );
endmodule
