// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tlul_socket_1n_bind;

  bind tlul_socket_1n tlul_assert tlul_assert_host (
    .clk_i,
    .rst_ni,
    .h2d    (tl_h_i),
    .d2h    (tl_h_o)
  );

  // TODO(NilsGraf): because there are N of these tl_d_* interfaces, need to create
  // a new module tlul_assert_multiple, which instantiates N tlul_assert modules
  bind tlul_socket_1n tlul_assert tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d    (tl_d_o[0]),
    .d2h    (tl_d_i[0])
  );

endmodule
