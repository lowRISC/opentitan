// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface is used to detect when the external clock is activated and sub sequently
// deactivated, as part of hardening chip level test(s) enabling the external clock.
interface ast_ext_clk_if ();
  import uvm_pkg::*;

  task static detect_io_active_window();
    fork
      wait(u_ast.u_ast_clks_byp.u_clk_src_io_sel.clk_ext_en_o == 1'b1);
      `uvm_info("ast_ext_clk_if", "External clk became active for io clk", UVM_MEDIUM)
      wait(u_ast.u_ast_clks_byp.u_clk_src_io_sel.clk_osc_en_o == 1'b0);
      `uvm_info("ast_ext_clk_if", "External clk back to inactive for io clk", UVM_MEDIUM)
    join
  endtask

endinterface : ast_ext_clk_if
