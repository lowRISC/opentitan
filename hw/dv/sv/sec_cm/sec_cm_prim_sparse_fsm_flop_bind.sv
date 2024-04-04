// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module sec_cm_prim_sparse_fsm_flop_bind ();
`ifndef GATE_LEVEL
  bind prim_sparse_fsm_flop prim_sparse_fsm_flop_if #(
    .Width(Width),
    .CustomForceName(CustomForceName)
  ) u_prim_sparse_fsm_flop_if (.*);
`endif
endmodule
