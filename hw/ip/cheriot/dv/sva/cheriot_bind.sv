// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module cheriot_bind;

  bind cheriot tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device_regs (
    .clk_i,
    .rst_ni,
    .h2d  (regs_tl_d_i),
    .d2h  (regs_tl_d_o)
  );

  bind cheriot tlul_assert #(
    .EndpointType("Host")
  ) tlul_assert_host_cored (
    .clk_i,
    .rst_ni,
    .h2d  (cored_tl_h_o),
    .d2h  (cored_tl_h_i)
  );

  bind cheriot tlul_assert #(
    .EndpointType("Host")
  ) tlul_assert_host_tbre (
    .clk_i,
    .rst_ni,
    .h2d  (tbre_tl_h_o),
    .d2h  (tbre_tl_h_i)
  );

  bind cheriot tlul_assert #(
    .EndpointType("Host")
  ) tlul_assert_host_meta_sram (
    .clk_i,
    .rst_ni,
    .h2d  (meta_sram_tl_o),
    .d2h  (meta_sram_tl_i)
  );

  bind cheriot cheriot_regs_csr_assert_fpv cheriot_regs_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (regs_tl_d_i),
    .d2h    (regs_tl_d_o)
  );

endmodule
