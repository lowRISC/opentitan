// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module sec_cm_prim_onehot_check_bind ();
`ifndef GATE_LEVEL
  bind prim_onehot_check prim_onehot_check_if #(
    .AddrWidth  (AddrWidth),
    .OneHotWidth(OneHotWidth),
    .AddrCheck  (AddrCheck),
    .EnableCheck(EnableCheck),
    .StrictCheck(StrictCheck)
  ) u_prim_onehot_check_if (.*);
`endif
endmodule
