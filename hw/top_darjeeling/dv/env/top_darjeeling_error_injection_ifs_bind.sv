// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This adds interfaces that enable error injection in selected modules.
module top_darjeeling_error_injection_ifs_bind;
`ifndef GATE_LEVEL
  // This is used to inject count errors in clkmgr.
  bind tb.dut.top_darjeeling.u_clkmgr_aon.u_clk_main_aes_trans.u_idle_cnt prim_count_if
    prim_count_if(.*);
  // This is used to inject reset consistency errors in rstmgr.
  bind rstmgr_leaf_rst rstmgr_cnsty_fault_if rstmgr_cnsty_fault_if (.*);
`endif
endmodule
