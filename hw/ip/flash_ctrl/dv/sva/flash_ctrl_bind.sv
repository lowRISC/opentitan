// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module flash_ctrl_bind;

  bind flash_ctrl tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (core_tl_i),
    .d2h  (core_tl_o)
  );

  bind flash_ctrl flash_ctrl_core_csr_assert_fpv flash_ctrl_core_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (core_tl_i),
    .d2h    (core_tl_o)
  );

  bind flash_ctrl flash_ctrl_dv_if flash_ctrl_dv_if (
    .clk_i,
    .rst_ni,
    .rd_buf_en (u_flash_hw_if.rd_buf_en_o),
    .rma_req (u_flash_hw_if.rma_req_i),
    .rma_state (u_flash_hw_if.rma_state_q),
    .lcmgr_state (u_flash_hw_if.state_q)
  );
endmodule
