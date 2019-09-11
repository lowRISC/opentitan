// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tlul_socket_m1_bind;

  bind tlul_socket_m1 tlul_assert_multiple #(M) tlul_assert_host (
    .clk_i,
    .rst_ni,
    .h2d    (tl_h_i),
    .d2h    (tl_h_o)
  );

  bind tlul_socket_m1 tlul_assert tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d    (tl_d_o),
    .d2h    (tl_d_i)
  );

endmodule
