// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module prim_max_tree_bind_fpv;


  bind prim_max_tree prim_max_tree_assert_fpv #(
    .NumSrc(NumSrc),
    .Width(Width)
  ) i_prim_max_tree_assert_fpv (
    .clk_i,
    .rst_ni,
    .values_i,
    .valid_i,
    .max_value_o,
    .max_idx_o,
    .max_valid_o
  );


endmodule : prim_max_tree_bind_fpv
