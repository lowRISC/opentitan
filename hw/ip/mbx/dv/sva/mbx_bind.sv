// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module mbx_bind;

  // Bind assertion module to RoT-side SRAM interface
  bind mbx tlul_assert #(
    .EndpointType("Host")
  ) sram_tlul_assert_core (
    .clk_i,
    .rst_ni,
    .h2d  (sram_tl_h_o),
    .d2h  (sram_tl_h_i)
  );

  // Bind assertion module to RoT-side config interface
  bind mbx tlul_assert #(
    .EndpointType("Device")
  ) core_tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (core_tl_d_i),
    .d2h  (core_tl_d_o)
  );

  // Bind assertion module to SoC-side config interface
  bind mbx tlul_assert #(
    .EndpointType("Device")
  ) soc_tlul_assert_device(
    .clk_i,
    .rst_ni,
    .h2d  (soc_tl_d_i),
    .d2h  (soc_tl_d_o)
  );

  // TODO: Revisit this
  //bind mbx mbx_csr_assert_fpv mbx_csr_assert (
  //   .clk_i,
  //   .rst_ni,
  //   .h2d (core_tl_d_i),
  //   .d2h (core_tl_d_o)
  //);

endmodule
