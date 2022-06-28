// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface is used to detect when the external clock is activated and sub sequently
// deactivated, as part of hardening chip level test(s) enabling the external clock.
interface ast_ext_clk_if ();
  import uvm_pkg::*;

  string msg_id = "ast_ext_clk_if";

  task automatic detect_io_active_window();
    fork
      wait(u_ast.u_ast_clks_byp.u_io_clk_byp_en.out_o == 1'b1);
      `uvm_info("ast_ext_clk_if", "External clk became active for io clk", UVM_MEDIUM)
      wait(u_ast.u_ast_clks_byp.u_io_clk_osc_en.out_o == 1'b0);
      `uvm_info("ast_ext_clk_if", "External clk back to inactive for io clk", UVM_MEDIUM)
    join
  endtask

  function automatic void check_ext_clk_in_use();
    `DV_CHECK_EQ(u_ast.u_ast_clks_byp.u_io_clk_osc_en.out_o, 0, , , msg_id)
  endfunction

endinterface : ast_ext_clk_if
