// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Bind prim_diff_decode_assert_fpv into each instance of prim_diff_decode in the design.

module prim_diff_decode_bind_fpv;
  bind prim_diff_decode prim_diff_decode_assert_fpv
    #(.AsyncOn (AsyncOn)) u_assert_fpv (.clk_i, .rst_ni);
endmodule
