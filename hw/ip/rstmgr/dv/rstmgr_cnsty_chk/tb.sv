// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for rstmgr_cnsty_chk.
//
// Checks that errors are flagged for the following cases.
// - Child reset going active with inactive reset requests.
// - Child reset going inactive with active reset requests.
//
// NB: The checks are triggered by the reference clock.
interface rstmgr_cnsty_chk_if;
  logic child_rst_ni;
  logic parent_rst_ni;
  logic sw_rst_req_i;
  logic sw_rst_req_clr_o;
  logic err_o;
  logic fsm_err_o;
endinterface

class reset_class;

  parameter time ClkPeriod = 10_000;
  parameter time ChildFastClkPeriod = 6_000;
  parameter time ChildSlowClkPeriod = 25_000;

  import uvm_pkg::*;

  typedef enum int {
    OrderChildLags,
    OrderChildLeads
  } order_e;

  typedef enum int {
    TimingOkay,
    TimingSlow
  } timing_e;

  typedef enum int {
    ChildClkFaster,
    ChildClkSlower
  } child_clk_e;

  typedef struct packed {
    order_e order;
    timing_e timing;
  } reset_op_t;

  virtual clk_rst_if clk_rst_vif;
  virtual clk_rst_if child_clk_rst_vif;
  virtual rstmgr_cnsty_chk_if reset_vif;

  logic error = 0;
  int cycles_to_check = 7;

  rand int cycles_reset_width;
  rand int cycles_child_reset_width;
  rand int cycles_in_apply_resets;
  rand int cycles_to_child_reset;
  rand int cycles_to_child_release;
  rand int cycles_to_parent_reset;
  rand int cycles_to_parent_release;
  rand int cycles_to_sw_reset;
  rand int cycles_to_sw_release;

  constraint cycles_reset_width_c {cycles_reset_width inside {[2 : 10]};}
  constraint cycles_child_reset_width_c {cycles_child_reset_width inside {[2 : 10]};}
  constraint cycles_in_apply_resets_c {cycles_in_apply_resets inside {[5 : 25]};}
  constraint cycles_to_child_reset_c {cycles_to_child_reset inside {[3 : 8]};}
  constraint cycles_to_child_release_c {cycles_to_child_release inside {[3 : 6]};}
  constraint cycles_to_parent_reset_c {cycles_to_parent_reset inside {[2 : 8]};}
  constraint cycles_to_parent_release_c {cycles_to_parent_release inside {[3 : 6]};}
  constraint cycles_to_sw_reset_c {cycles_to_sw_reset inside {[2 : 8]};}
  constraint cycles_to_sw_release_c {cycles_to_sw_release inside {[3 : 6]};}

  function new(virtual clk_rst_if clk_vif, virtual clk_rst_if child_clk_vif,
               virtual rstmgr_cnsty_chk_if rst_vif);
    clk_rst_vif = clk_vif;
    child_clk_rst_vif = child_clk_vif;
    reset_vif = rst_vif;
  endfunction

  function string get_full_name();
    return "reset_class";
  endfunction

  task set_child_period(child_clk_e child_clk);
    if (child_clk == ChildClkFaster) begin
      `uvm_info(`gfn, $sformatf(
                "Setting child clk (%0d ps) faster than reference (%0d ps)",
                ChildFastClkPeriod,
                ClkPeriod
                ), UVM_LOW)
      child_clk_rst_vif.set_period_ps(ChildFastClkPeriod);
    end else begin
      `uvm_info(`gfn, $sformatf(
                "Setting child clk (%0d ps) slower than reference (%0d ps)",
                ChildSlowClkPeriod,
                ClkPeriod
                ), UVM_LOW)
      child_clk_rst_vif.set_period_ps(ChildSlowClkPeriod);
    end
  endtask

  task apply_resets();
    fork
      clk_rst_vif.apply_reset(.reset_width_clks(cycles_reset_width));
      child_clk_rst_vif.apply_reset(.reset_width_clks(cycles_child_reset_width));
      begin
        reset_vif.parent_rst_ni = 1'b0;
        clk_rst_vif.wait_clks(cycles_in_apply_resets);
        reset_vif.parent_rst_ni = 1'b1;
      end
    join
    clk_rst_vif.wait_clks(4);
  endtask

  task set_quiescent();
    `uvm_info(`gfn, "Setting quiescent inputs", UVM_MEDIUM)
    reset_vif.parent_rst_ni = 1'b1;
    reset_vif.sw_rst_req_i  = 1'b0;
    reset_vif.child_rst_ni  = 1'b1;
  endtask

  task set_parent_reset(logic value, int cycles);
    clk_rst_vif.wait_clks(cycles_to_parent_reset);
    `uvm_info(`gfn, $sformatf("Setting parent_rst_ni=%b", value), UVM_MEDIUM)
    reset_vif.parent_rst_ni = value;
  endtask

  task set_sw_reset(logic value, int cycles);
    clk_rst_vif.wait_clks(cycles_to_sw_reset);
    `uvm_info(`gfn, $sformatf("Setting sw_rst_req_i=%b", value), UVM_MEDIUM)
    reset_vif.sw_rst_req_i = value;
  endtask

  task set_child_reset(logic value, int cycles);
    clk_rst_vif.wait_clks(cycles);
    `uvm_info(`gfn, $sformatf("Setting child_rst_ni=%b", value), UVM_MEDIUM)
    reset_vif.child_rst_ni = value;
  endtask

  task send_unexpected_child_resets();
    `uvm_info(`gfn, "check unexpected active child reset", UVM_MEDIUM)
    set_child_reset(.value(0), .cycles(cycles_to_child_reset));
    clk_rst_vif.wait_clks(cycles_to_check);
    `DV_CHECK_EQ(reset_vif.err_o, 1'b1, "expected error for unexpected active child reset")
    clk_rst_vif.wait_clks(cycles_to_child_release);
    reset_vif.child_rst_ni = 1'b1;
  endtask

  task send_unexpected_child_release();
    `uvm_info(`gfn, "check unexpected inactive child reset", UVM_MEDIUM)
    fork
      set_parent_reset(.value(0), .cycles(cycles_to_parent_reset));
      set_sw_reset(.value(1), .cycles(cycles_to_sw_reset));
      set_child_reset(.value(0), .cycles(cycles_to_child_reset));
    join
    clk_rst_vif.wait_clks(cycles_to_child_release);
    reset_vif.child_rst_ni = 1'b1;
    clk_rst_vif.wait_clks(cycles_to_check);
    `uvm_info(`gfn, "Checking err_o output", UVM_MEDIUM)
    `DV_CHECK_EQ(reset_vif.err_o, 1'b1, "expected error for unexpected inactive child reset")
  endtask

  task unexpected_child_activity();
    `uvm_info(`gfn, "checking unexpected child activity", UVM_LOW)
    for (int i = 0; i < 20; ++i) begin
      set_quiescent();
      `DV_CHECK_RANDOMIZE_FATAL(this);

      send_unexpected_child_resets();
      // Expect an error, so reset the dut.
      apply_resets();

      send_unexpected_child_release();
      apply_resets();
    end
  endtask

  task body();
    clk_rst_vif.set_period_ps(ClkPeriod);
    clk_rst_vif.set_active();
    child_clk_rst_vif.set_period_ps(ChildFastClkPeriod);
    child_clk_rst_vif.set_active();
    `DV_CHECK_RANDOMIZE_FATAL(this);

    set_quiescent();
    apply_resets();

    // Run with child clock faster than reference.
    set_child_period(ChildClkFaster);
    clk_rst_vif.wait_clks(20);

    unexpected_child_activity();

    // Run with child clock slower than reference.
    set_child_period(ChildClkSlower);
    clk_rst_vif.wait_clks(20);

    unexpected_child_activity();
  endtask
endclass

module tb;

  import uvm_pkg::*;

  reset_class reset_cl;

  wire clk_i;
  wire rst_ni;
  wire child_clk_i;
  wire unused_child_rst_ni;

  clk_rst_if clk_rst_if (
    .clk  (clk_i),
    .rst_n(rst_ni)
  );
  clk_rst_if child_clk_rst_if (
    .clk  (child_clk_i),
    .rst_n(unused_child_rst_ni)
  );
  rstmgr_cnsty_chk_if rstmgr_cnsty_chk_if ();

  logic error = 0;

  rstmgr_cnsty_chk dut (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .child_clk_i(child_clk_i),
    .child_rst_ni(rstmgr_cnsty_chk_if.child_rst_ni),
    .parent_rst_ni(rstmgr_cnsty_chk_if.parent_rst_ni),
    .sw_rst_req_i(rstmgr_cnsty_chk_if.sw_rst_req_i),
    .sw_rst_req_clr_o(rstmgr_cnsty_chk_if.sw_rst_req_clr_o),
    .err_o(rstmgr_cnsty_chk_if.err_o),
    .fsm_err_o(rstmgr_cnsty_chk_if.fsm_err_o)
  );

  // set this to one to avoid a SVA error
  // This SVA is to ensure we have a fatal alert check attached to the FSM error, but this is unit
  // level testbench, no alert will occur.
  assign dut.u_state_regs.unused_assert_connected = 1;
  initial begin
    automatic dv_utils_pkg::dv_report_server dv_report_server = new();
    $timeformat(-12, 0, " ps", 12);
    uvm_report_server::set_server(dv_report_server);
    reset_cl = new(clk_rst_if, child_clk_rst_if, rstmgr_cnsty_chk_if);
    reset_cl.body();
    dv_report_server.report_summarize();
    $finish();
  end

endmodule : tb
