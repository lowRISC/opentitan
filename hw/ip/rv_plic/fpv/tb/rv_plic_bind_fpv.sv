// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module rv_plic_bind_fpv;
  bind rv_plic rv_plic_assert_fpv rv_plic_assert_fpv (
    .clk_i,
    .rst_ni,
    .intr_src_i,
    .irq_o,
    .irq_id_o,
    .msip_o
  );
endmodule : rv_plic_bind_fpv
