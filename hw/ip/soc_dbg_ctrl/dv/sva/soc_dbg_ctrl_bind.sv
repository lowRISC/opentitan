// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module soc_dbg_ctrl_bind;
  bind soc_dbg_ctrl tlul_assert #(
    .EndpointType("Device")
  ) tlul_core_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (core_tl_i),
    .d2h  (core_tl_o)
  );

  bind soc_dbg_ctrl soc_dbg_ctrl_core_csr_assert_fpv soc_dbg_ctrl_core_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d  (core_tl_i),
    .d2h  (core_tl_o)
  );

  bind soc_dbg_ctrl tlul_assert #(
    .EndpointType("Device")
    ) tlul_jtag_assert_device (
      .clk_i,
      .rst_ni,
      .h2d  (jtag_tl_i),
      .d2h  (jtag_tl_o)
  );

  bind soc_dbg_ctrl soc_dbg_ctrl_jtag_csr_assert_fpv soc_dbg_ctrl_jtag_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d  (jtag_tl_i),
    .d2h  (jtag_tl_o)
  );
endmodule : soc_dbg_ctrl_bind
