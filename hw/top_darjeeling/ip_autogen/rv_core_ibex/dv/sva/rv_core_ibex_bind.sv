// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module rv_core_ibex_bind;

  bind rv_core_ibex tlul_assert #(
    .EndpointType("Host")
  ) tlul_assert_host_instr (
    .clk_i,
    .rst_ni,
    .h2d  (corei_tl_h_o),
    .d2h  (corei_tl_h_i)
  );

  bind rv_core_ibex tlul_assert #(
    .EndpointType("Host")
  ) tlul_assert_host_data (
    .clk_i,
    .rst_ni,
    .h2d  (cored_tl_h_o),
    .d2h  (cored_tl_h_i)
  );

  bind rv_core_ibex tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device_cfg (
    .clk_i,
    .rst_ni,
    .h2d  (cfg_tl_d_i),
    .d2h  (cfg_tl_d_o)
  );

endmodule
