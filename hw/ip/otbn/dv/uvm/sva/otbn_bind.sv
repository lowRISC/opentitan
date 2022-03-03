// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_bind;

  bind otbn tlul_assert #(
    .EndpointType("Device")
  ) tlul_checker (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .h2d    (tl_i),
    .d2h    (tl_o)
  );

  bind otbn otbn_csr_assert_fpv csr_checker (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .h2d    (tl_i),
    .d2h    (tl_o)
  );

  bind otbn otbn_idle_checker idle_checker (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .reg2hw   (reg2hw),
    .hw2reg   (hw2reg),
    .done_i   (done),
    .idle_o_i (idle_o),

    .otbn_dmem_scramble_key_req_busy_i(otbn_dmem_scramble_key_req_busy),
    .otbn_imem_scramble_key_req_busy_i(otbn_imem_scramble_key_req_busy),

    .status_q_i(reg2hw.status.q)
  );

endmodule
