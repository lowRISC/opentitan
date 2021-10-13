// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface is used to force the voltage supply indicators, to trigger resets due to
// power-not-ok conditions.
//
// The glitches of interest are on the vcaon_supp_i and vcmain_supp_i AST inputs.
// Forcing the values to 0 causes the AST to deassert the corresponding pok output: vcaon should
// cause a POR reset, and vcmain a non-aon reset.
//
// We need to disable some pwrmgr design assertions when wiggling vcmain_supp_i.
interface ast_supply_if (
  input logic clk,
  input logic trigger
);

  // The number of cycles to hold the glitch. It should be ok if it was just 1.
  localparam int CyclesGlitching = 3;

  // The number of cycles after stopping the glitch in vcmain before restarting
  // assertions in pwrmgr.
  localparam int CyclesBeforeReenablingAssert = 7;

  function static void force_vcaon_supp_i(bit value);
    force u_ast.vcaon_supp_i = value;
  endfunction

  // Wait some clock cycles due to various flops in the logic.
  task automatic reenable_vcmain_assertion();
    repeat (CyclesBeforeReenablingAssert) @(posedge clk);
    `uvm_info("ast_supply_if", "re-enabling vcmain_supp_i related SVA", UVM_MEDIUM)
    $assertcontrol(3, 1, 1, 1, top_earlgrey.u_pwrmgr_aon.u_slow_fsm.IntRstReq_A);
  endtask

  task static force_vcmain_supp_i(bit value);
    `uvm_info("ast_supply_if", $sformatf("forcing vcmain_supp_i to %b", value), UVM_MEDIUM)
    if (!value) begin
      `uvm_info("ast_supply_if", "disabling vcmain_supp_i related SVA", UVM_MEDIUM)
      $assertcontrol(4, 1, 1, 1, top_earlgrey.u_pwrmgr_aon.u_slow_fsm.IntRstReq_A);
    end
    force u_ast.vcmain_supp_i = value;
    if (value) reenable_vcmain_assertion();
  endtask

  // Create glitch in vcmain_supp_i some cycles after a trigger transitions high.
  task automatic glitch_vcmain_supp_i_on_next_trigger(int cycles);
    @(posedge trigger);
    repeat (cycles) @(posedge clk);
    force_vcmain_supp_i(1'b0);
    repeat (CyclesGlitching) @(posedge clk);
    force_vcmain_supp_i(1'b1);
  endtask

endinterface
