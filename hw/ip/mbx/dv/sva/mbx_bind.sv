// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module mbx_bind;

  bind mbx tlul_assert #(
    .EndpointType("Host")
  ) mbx_agx_tlul_assert_core (
    .clk_i(hstRegAccL3),
    .rst_ni(hstRegReset),
    .h2d  (mbx_agx_tlReQH2d),
    .d2h  (agx_mbx_tlRsPD2h)
  );

  bind mbx tlul_assert #(
    .EndpointType("Device")
  ) agx_mbx_tlul_assert_device (
    .clk_i(hstRegAccL3),
    .rst_ni(hstRegReset),
    .h2d  (agx_mbx_tlReQH2d),
    .d2h  (mbx_agx_tlRsPD2h)
  );

  bind mbx tlul_assert #(
    .EndpointType("Device")
  ) scx_mbx_tlul_assert_device(
    .clk_i(sysRegAccL3),
    .rst_ni(sysRegReset),
    .h2d  (scx_mbx_tlReQH2d),
    .d2h  (mbx_scx_tlRsPD2h)
  );

  // TODO: Revisit this
  // bind mbx mbx_regs_csr_assert_fpv mbx_regs_csr_assert (
  //   .clk_i,
  //   .rst_ni,
  //   .h2d    (regs_tl_i),
  //   .d2h    (regs_tl_o)
  // );

endmodule
