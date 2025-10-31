// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module rram_ctrl_bind;

  bind rram_ctrl tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  bind rram_ctrl rram_ctrl_csr_assert_fpv rram_ctrl_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o)
  );

  bind rram_ctrl tlul_assert #(
    .EndpointType("Device")
  ) tlul_host_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (host_tl_i),
    .d2h  (host_tl_o)
  );

  bind rram_ctrl rram_ctrl_host_csr_assert_fpv rram_ctrl_host_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d  (host_tl_i),
    .d2h  (host_tl_o)
  );

  bind rram_ctrl tlul_assert #(
    .EndpointType("Device")
    ) tlul_prim_assert_device (
      .clk_i,
      .rst_ni,
      .h2d  (prim_tl_i),
      .d2h  (prim_tl_o)
  );

  bind rram_ctrl rram_ctrl_prim_csr_assert_fpv rram_ctrl_prim_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d  (prim_tl_i),
    .d2h  (prim_tl_o)
  );
endmodule : rram_ctrl_bind
