// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface enables hardening tests that expect to use the external clock by sampling an ast
// external clock enable signal.
interface ast_ext_clk_if ();
  import uvm_pkg::*;

  // A timeout in case something holds the expected change.
  localparam int WaitForExctClkSelChangeInNs = 10_000_000;

  // This task returns once the external clock has gone through an active cycle.
  // Notice it will fail if the active cycle has already started.
  task automatic span_external_clock_active_window();
    `DV_WAIT(u_ast.u_ast_clks_byp.u_io_clk_byp_en.out_o == 1'b1,
                 "Took too long to enable external clock", WaitForExctClkSelChangeInNs,
                 "ast_ext_clk_if")
    `uvm_info("ast_ext_clk_if", "External clk became active for io clk", UVM_MEDIUM)
    `DV_WAIT(u_ast.u_ast_clks_byp.u_io_clk_byp_en.out_o == 1'b0,
                 "Took too long to disable external clock", WaitForExctClkSelChangeInNs,
                 "ast_ext_clk_if")
    `uvm_info("ast_ext_clk_if", "External clk back to inactive for io clk", UVM_MEDIUM)
  endtask

  // Returns 1 if the external clock is in use.
  function automatic logic is_ext_clk_in_use();
    return u_ast.u_ast_clks_byp.u_io_clk_byp_en.out_o;
  endfunction

endinterface : ast_ext_clk_if
