// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module sec_cm_bind();
  bind prim_count prim_count_if #(.CntStyle(CntStyle), .Width(Width)) u_prim_count_if (.*);

  bind prim_sparse_fsm_flop prim_sparse_fsm_flop_if #(
         .Width(Width)) u_prim_sparse_fsm_flop_if (.*);
endmodule
