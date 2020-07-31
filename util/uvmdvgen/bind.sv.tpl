// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ${name}_bind;
% if is_cip:

  bind ${name} tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );
% endif
% if has_ral:

  import ${name}_reg_pkg::*;
  bind ${name} ${name}_csr_assert_fpv ${name}_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o),
    .reg2hw (reg2hw),
    .hw2reg (hw2reg)
  );
% endif

endmodule
