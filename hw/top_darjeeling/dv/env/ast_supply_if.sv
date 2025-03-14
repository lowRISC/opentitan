// Copyright lowRISC contributors (OpenTitan project).
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
  input logic core_sleeping_trigger,
  input logic low_power_trigger
);
  import uvm_pkg::*;

  // The amount of time to hold the glitch. Should be enough to span more than one aon_clk cycles
  // so it is sampled.
  localparam time GlitchTimeSpan = 10us;
  localparam int GlitchCycles = 6;

  // The number of cycles after stopping the glitch in vcmain before restarting
  // assertions in pwrmgr.
  localparam int CyclesBeforeReenablingAssert = 7;

  function static void force_vcaon_pok(bit value);
    force u_ast.u_rglts_pdm_3p3v.vcaon_pok_h_o = value;
  endfunction

  // Create glitch in vcaon_pok_h_o some cycles after this is invoked. Hold vcaon_pok_h_o low for
  // a fixed time: we cannot use clock cycles because the clock will stop.
  task automatic glitch_vcaon_pok(int cycles);
    repeat (cycles) @(posedge clk);
    `uvm_info("ast_supply_if", "forcing vcaon_pok_h_o=0", UVM_MEDIUM)
    force_vcaon_pok(1'b0);
    #(GlitchTimeSpan);
    `uvm_info("ast_supply_if", "forcing vcaon_pok_h_o=1", UVM_MEDIUM)
    force_vcaon_pok(1'b1);
  endtask

  // Wait some clock cycles due to various flops in the logic.
  task automatic reenable_vcmain_assertion();
`ifndef GATE_LEVEL
    repeat (CyclesBeforeReenablingAssert) @(posedge clk);
    `uvm_info("ast_supply_if", "re-enabling vcmain_supp_i related SVA", UVM_MEDIUM)
    $asserton(1, top_darjeeling.u_pwrmgr_aon.u_slow_fsm.IntRstReq_A);
`endif
  endtask

  task static force_vcmain_pok(bit value);
`ifndef GATE_LEVEL
    `uvm_info("ast_supply_if", $sformatf("forcing vcmain_pok_h_o to %b", value), UVM_MEDIUM)
    if (!value) begin
      `uvm_info("ast_supply_if", "disabling vcmain_supp_i related SVA", UVM_MEDIUM)
      $assertoff(1, top_darjeeling.u_pwrmgr_aon.u_slow_fsm.IntRstReq_A);
    end
    force u_ast.u_rglts_pdm_3p3v.vcmain_pok_h_o = value;
`endif
  endtask

`define GLITCH_VCMAIN_POK                 \
    force_vcmain_pok(1'b0);               \
    repeat (GlitchCycles) @(posedge clk); \
    force_vcmain_pok(1'b1)

  // Create glitch in vcmain_pok_h_o some cycles after core_sleeping trigger transitions high.
  // This is useful for non-deep sleep-related triggers.
  task automatic glitch_vcmain_pok_on_next_core_sleeping_trigger(int cycles);
    @(posedge core_sleeping_trigger);
    repeat (cycles) @(posedge clk);
    `GLITCH_VCMAIN_POK;
  endtask : glitch_vcmain_pok_on_next_core_sleeping_trigger

  // Create glitch in vcmain_pok_h_o once the fast fsm sets the reset cause to LowPwrEntry.
  task automatic glitch_vcmain_pok_on_next_low_power_trigger();
    @(posedge low_power_trigger);
    `GLITCH_VCMAIN_POK;
  endtask : glitch_vcmain_pok_on_next_low_power_trigger

`undef GLITCH_VCMAIN_POK

endinterface
