// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module rstmgr_fpv_bind;

  bind rstmgr u_csr_assert_fpv u_csr_assert_fpv (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

endmodule : rstmgr_bind_fpv
