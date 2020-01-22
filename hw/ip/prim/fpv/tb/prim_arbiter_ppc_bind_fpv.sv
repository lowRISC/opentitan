// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module prim_arbiter_ppc_bind_fpv;


  bind prim_arbiter_ppc prim_arbiter_ppc_assert_fpv #(
    .N(N),
    .DW(DW)
  ) i_prim_arbiter_ppc_assert_fpv (
    .clk_i,
    .rst_ni,
    .req_i,
    .data_i,
    .gnt_o,
    .idx_o,
    .valid_o,
    .data_o,
    .ready_i
  );


endmodule : prim_arbiter_ppc_bind_fpv
