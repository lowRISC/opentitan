// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module rom_ctrl_bind;

  bind rom_ctrl tlul_assert #(
    .EndpointType("Device")
  ) rom_tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (rom_tl_i),
    .d2h  (rom_tl_o)
  );

  bind rom_ctrl tlul_assert #(
    .EndpointType("Device")
  ) regs_tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (regs_tl_i),
    .d2h  (regs_tl_o)
  );

  bind rom_ctrl rom_ctrl_regs_csr_assert_fpv rom_ctrl_regs_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (regs_tl_i),
    .d2h    (regs_tl_o)
  );

endmodule
