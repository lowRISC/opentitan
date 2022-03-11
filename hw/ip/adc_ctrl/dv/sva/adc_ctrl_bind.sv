// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module adc_ctrl_bind;

  bind adc_ctrl tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d(tl_i),
    .d2h(tl_o)
  );

  bind adc_ctrl adc_ctrl_csr_assert_fpv adc_ctrl_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d(tl_i),
    .d2h(tl_o)
  );

  bind adc_ctrl_fsm adc_ctrl_fsm_sva u_adc_ctrl_fsm_sva (.*);
endmodule
