// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module dma_bind;

  // Bind assertion module to config interface
  bind dma tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_d_i),
    .d2h  (tl_d_o)
  );

  // Bind CSR assertion module on config interface
  bind dma dma_csr_assert_fpv dma_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (tl_d_i),
    .d2h    (tl_d_o)
  );

  // Bind assertion module to CTN interface
  bind dma tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_ctn (
    .clk_i,
    .rst_ni,
    .h2d  (ctn_tl_h2d_o),
    .d2h  (ctn_tl_d2h_i)
  );

  // Bind assertion module to HOST interface
  bind dma tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_host (
    .clk_i,
    .rst_ni,
    .h2d  (host_tl_h_o),
    .d2h  (host_tl_h_i)
  );

  // TODO: bins tlul_assert to SYS interface
endmodule
