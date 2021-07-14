// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module sram_ctrl_bind;

  bind sram_ctrl tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device_regs (
    .clk_i,
    .rst_ni,
    .h2d(regs_tl_i),
    .d2h(regs_tl_o)
  );

  bind sram_ctrl tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device_ram (
    .clk_i,
    .rst_ni,
    .h2d(ram_tl_i),
    .d2h(ram_tl_o)
  );

  bind sram_ctrl sram_ctrl_regs_csr_assert_fpv sram_ctrl_regs_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d(regs_tl_i),
    .d2h(regs_tl_o)
  );

endmodule
