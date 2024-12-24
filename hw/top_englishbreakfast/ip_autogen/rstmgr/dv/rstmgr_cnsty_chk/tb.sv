// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for rstmgr_cnsty_chk.
//
// The test runs pairs of events separated by a variable number of cycles in order to determine
// when errors are triggered.
//
// Consider events E1 and E2: it can send E1 from N cycles before E2 up to M cycles after it and
// any number of cycles in between.
//
// The event pairs considered are:
// - Parent reset active, child reset active
// - Sw reset active, child reset active
// - Parent reset inactive, child reset inactive
// - Sw reset inactive, child reset inactive
//
// There are two clocks involved, and it tests either one running faster then the other.
//
// In order to improve coverage it also injects sparse fsm errors.

// Interface driving the dut.
interface rstmgr_cnsty_chk_if;
  logic child_rst_ni;
  logic parent_rst_ni;
  logic sw_rst_req_i;
  logic sw_rst_req_clr_o;
  logic err_o;
  logic fsm_err_o;
endinterface

// Class generating stimulus.
class reset_class;
  parameter time ClkPeriod = 10_000;
  parameter time ChildFastClkPeriod = 6_543;
  parameter time ChildSlowClkPeriod = 25_678;

  parameter int ScanSweepBeforeCycles = 50;
  parameter int ScanSweepAfterCycles = 10;
  parameter int ScanSweepCycles = ScanSweepBeforeCycles + ScanSweepAfterCycles;

  parameter int IterationsPerDelta = 16;

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
  int cycles_to_check = 8;

  bit parent_rst_n;
  bit sw_reset;

  int cycles_to_child_reset;
  int cycles_to_child_release;
  int cycles_to_parent_reset;
  int cycles_to_parent_release;
  int cycles_to_sw_reset;
  int cycles_to_sw_release;

  rand int cycles_reset_width;
  rand int cycles_child_reset_width;
  rand int cycles_in_apply_resets;

  constraint cycles_reset_width_c {cycles_reset_width inside {[2 : 10]};}
  constraint cycles_child_reset_width_c {cycles_child_reset_width inside {[2 : 10]};}
  constraint cycles_in_apply_resets_c {cycles_in_apply_resets inside {[5 : 25]};}

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
    `uvm_info(`gfn, "Start apply_resets", UVM_MEDIUM)
    fork
      clk_rst_vif.apply_reset(.reset_width_clks(cycles_reset_width));
      child_clk_rst_vif.apply_reset(.reset_width_clks(cycles_child_reset_width));
      begin
        reset_vif.parent_rst_ni = 1'b0;
        clk_rst_vif.wait_clks(cycles_in_apply_resets);
        reset_vif.parent_rst_ni = 1'b1;
      end
      begin
        reset_vif.child_rst_ni = 1'b0;
        child_clk_rst_vif.wait_clks(cycles_in_apply_resets);
        reset_vif.child_rst_ni = 1'b1;
      end
    join
    clk_rst_vif.wait_clks(20);
    `uvm_info(`gfn, "End apply_resets", UVM_MEDIUM)
  endtask

  task set_quiescent();
    `uvm_info(`gfn, "Setting quiescent inputs", UVM_MEDIUM)
    reset_vif.parent_rst_ni = 1'b1;
    reset_vif.sw_rst_req_i  = 1'b0;
    reset_vif.child_rst_ni  = 1'b1;
  endtask

  task set_parent_reset(logic value, int cycles);
    if (reset_vif.parent_rst_ni == value) return;
    `uvm_info(`gfn, $sformatf("Setting parent_rst_ni=%b after %0d cycles", value, cycles), UVM_HIGH)
    clk_rst_vif.wait_clks(cycles);
    reset_vif.parent_rst_ni = value;
  endtask

  task set_sw_reset(logic value, int cycles);
    if (reset_vif.sw_rst_req_i == value) return;
    `uvm_info(`gfn, $sformatf("Setting sw_rst_req_i=%b after %0d cycles", value, cycles), UVM_HIGH)
    clk_rst_vif.wait_clks(cycles);
    reset_vif.sw_rst_req_i = value;
  endtask

  task set_child_reset(logic value, int cycles);
    if (reset_vif.child_rst_ni == value) return;
    `uvm_info(`gfn, $sformatf("Setting child_rst_ni=%b after %0d cycles", value, cycles), UVM_HIGH)
    clk_rst_vif.wait_clks(cycles);
    reset_vif.child_rst_ni = value;
  endtask

  task reset_start();
    fork
      set_parent_reset(.value(parent_rst_n), .cycles(cycles_to_parent_reset));
      set_sw_reset(.value(sw_reset), .cycles(cycles_to_sw_reset));
      set_child_reset(.value(0), .cycles(cycles_to_child_reset));
    join
  endtask

  task reset_end();
    fork
      set_parent_reset(.value(1), .cycles(cycles_to_parent_release));
      set_sw_reset(.value(0), .cycles(cycles_to_sw_release));
      set_child_reset(.value(1), .cycles(cycles_to_child_release));
    join
  endtask

  // Run a number of reset scenarios with some given cycle delays to allow CDC cycle fluctuations.
  task run_iterations(input string description, input int delta_cycles, output int error_count);
    error_count = 0;
    for (int i = 0; i < IterationsPerDelta; ++i) begin
      set_quiescent();
      reset_start();
      clk_rst_vif.wait_clks(20);
      reset_end();
      clk_rst_vif.wait_clks(cycles_to_check);
      if (reset_vif.err_o) begin
        ++error_count;
      end
      `uvm_info(`gfn, $sformatf(
                "Scan %0s with cycles delta %0d error %b",
                description,
                delta_cycles,
                reset_vif.err_o
                ), UVM_HIGH)
      // May get error, so reset.
      set_quiescent();
      apply_resets();
    end
  endtask

  // Run a parent reset to child reset.
  task scan_parent_rst();
    `uvm_info(`gfn, "scanning parent resets", UVM_LOW)
    sw_reset = 0;
    parent_rst_n = 0;
    cycles_to_parent_release = 4;
    cycles_to_child_release = 5;
    cycles_to_child_reset = ScanSweepBeforeCycles;
    for (
        cycles_to_parent_reset = 0;
        cycles_to_parent_reset < ScanSweepCycles;
        ++cycles_to_parent_reset
    ) begin
      int error_count = 0;
      int delta_cycles = cycles_to_parent_reset - cycles_to_child_reset;
      `uvm_info(`gfn, $sformatf("Sending parent reset %0d cycles from child", delta_cycles),
                UVM_MEDIUM)
      run_iterations("parent reset", delta_cycles, error_count);
      `uvm_info(`gfn, $sformatf(
                "Scan parent reset with cycles delta %0d total errors %0d / %0d",
                delta_cycles,
                error_count,
                IterationsPerDelta
                ), UVM_LOW)
      `DV_CHECK(((delta_cycles <= -4) || (delta_cycles >= 4)) || (error_count == 0))
      `DV_CHECK(((delta_cycles >= -5) && (delta_cycles <= 5)) ||
                (error_count == IterationsPerDelta))
    end
  endtask

  task scan_parent_release();
    `uvm_info(`gfn, "scanning parent release", UVM_LOW)
    sw_reset = 0;
    parent_rst_n = 0;
    cycles_to_parent_reset = 5;
    cycles_to_child_reset = 5;
    cycles_to_child_release = ScanSweepBeforeCycles;
    for (
        cycles_to_parent_release = 0;
        cycles_to_parent_release < ScanSweepCycles;
        ++cycles_to_parent_release
    ) begin
      int error_count = 0;
      int delta_cycles = cycles_to_parent_release - cycles_to_child_release;
      `uvm_info(`gfn, $sformatf("Sending parent release %0d cycles from child", delta_cycles),
                UVM_MEDIUM)
      run_iterations("parent release", delta_cycles, error_count);
      `uvm_info(`gfn, $sformatf(
                "Scan parent release with cycles delta %0d total errors %0d / %0d",
                delta_cycles,
                error_count,
                IterationsPerDelta
                ), UVM_LOW)
      `DV_CHECK((delta_cycles < -12) || (delta_cycles > -1) || (error_count == 0))
      `DV_CHECK(((delta_cycles > -42) && (delta_cycles < 2)) || (error_count == IterationsPerDelta))
    end
  endtask

  task scan_sw_rst();
    `uvm_info(`gfn, "scanning sw resets", UVM_LOW)
    sw_reset = 1;
    parent_rst_n = 1;
    cycles_to_sw_release = 4;
    cycles_to_child_release = 5;
    cycles_to_child_reset = ScanSweepBeforeCycles;
    for (cycles_to_sw_reset = 0; cycles_to_sw_reset < ScanSweepCycles; ++cycles_to_sw_reset) begin
      int error_count = 0;
      int delta_cycles = cycles_to_sw_reset - cycles_to_child_reset;
      `uvm_info(`gfn, $sformatf("Sending sw reset %0d cycles from child", delta_cycles), UVM_HIGH)
      run_iterations("sw reset", delta_cycles, error_count);
      `uvm_info(`gfn, $sformatf(
                "Scan sw reset with cycles delta %0d total errors %0d / %0d",
                delta_cycles,
                error_count,
                IterationsPerDelta
                ), UVM_LOW)
      `DV_CHECK((delta_cycles >= 3) || (error_count == 0))
      `DV_CHECK((delta_cycles <= 3) || (error_count == IterationsPerDelta))
    end
  endtask

  task scan_sw_release();
    `uvm_info(`gfn, "scanning sw releases", UVM_LOW)
    sw_reset = 1;
    parent_rst_n = 1;
    cycles_to_sw_reset = 4;
    cycles_to_child_reset = 5;
    cycles_to_child_release = ScanSweepBeforeCycles;
    for (
        cycles_to_sw_release = 0; cycles_to_sw_release < ScanSweepCycles; ++cycles_to_sw_release
    ) begin
      int error_count = 0;
      int delta_cycles = cycles_to_sw_release - cycles_to_child_release;
      `uvm_info(`gfn, $sformatf("Sending sw release %0d cycles from child", delta_cycles), UVM_HIGH)
      run_iterations("sw release", delta_cycles, error_count);
      `uvm_info(`gfn, $sformatf(
                "Scan sw release with cycles delta %0d total errors %0d / %0d",
                delta_cycles,
                error_count,
                IterationsPerDelta
                ), UVM_LOW)
      `DV_CHECK((delta_cycles < -8) || (delta_cycles > 3) || (error_count == 0))
      `DV_CHECK(((delta_cycles > -38) && (delta_cycles < 5)) || (error_count == IterationsPerDelta))
    end
  endtask

  task inject_fsm_errors();
    sec_cm_pkg::sec_cm_base_if_proxy if_proxy = sec_cm_pkg::find_sec_cm_if_proxy(
        "tb.dut.u_state_regs", 0
    );
    `DV_CHECK(!reset_vif.fsm_err_o)
    repeat (10) begin
      clk_rst_vif.wait_clks(5);
      if_proxy.inject_fault();
      clk_rst_vif.wait_clks(5);
      if_proxy.restore_fault();
      `DV_CHECK(reset_vif.fsm_err_o)
      apply_resets();
      `DV_CHECK(!reset_vif.fsm_err_o)
    end
    clk_rst_vif.wait_clks(5);
  endtask

  task body();
    foreach (sec_cm_pkg::sec_cm_if_proxy_q[i]) begin
      `uvm_info(`gfn, $sformatf("Path of proxy: %0s", sec_cm_pkg::sec_cm_if_proxy_q[i].path),
                UVM_MEDIUM)
    end
    clk_rst_vif.set_period_ps(ClkPeriod);
    clk_rst_vif.set_active();
    child_clk_rst_vif.set_period_ps(ChildFastClkPeriod);
    child_clk_rst_vif.set_active();
    `DV_CHECK_RANDOMIZE_FATAL(this);

    `uvm_info(`gfn, "Past set active", UVM_MEDIUM)
    set_quiescent();
    apply_resets();

    // Run with child clock faster than reference.
    set_child_period(ChildClkFaster);
    clk_rst_vif.wait_clks(20);

    set_quiescent();
    apply_resets();
    scan_parent_rst();

    set_quiescent();
    apply_resets();
    scan_parent_release();

    set_quiescent();
    apply_resets();
    scan_sw_rst();

    set_quiescent();
    apply_resets();
    scan_sw_release();

    set_quiescent();
    apply_resets();

    // Run with child clock slower than reference.
    set_child_period(ChildClkSlower);
    clk_rst_vif.wait_clks(20);

    set_quiescent();
    apply_resets();
    scan_parent_rst();

    set_quiescent();
    apply_resets();
    scan_parent_release();

    set_quiescent();
    apply_resets();
    scan_sw_rst();

    set_quiescent();
    apply_resets();
    scan_sw_release();

    // And inject sparse fsm errors.
    set_quiescent();
    apply_resets();
    inject_fsm_errors();
  endtask
endclass

module tb;

  import uvm_pkg::*;

  reset_class reset_cl;

  wire clk_i;
  wire rst_ni;
  wire child_clk_i;
  wire unused_child_rst_ni;

  bind prim_sparse_fsm_flop prim_sparse_fsm_flop_if #(
    .Width(Width),
    .CustomForceName(CustomForceName)
  ) prim_sparse_fsm_flop_if (.*);

  clk_rst_if clk_rst_if (
    .clk  (clk_i),
    .rst_n(rst_ni)
  );
  clk_rst_if child_clk_rst_if (
    .clk  (child_clk_i),
    .rst_n(child_rst_ni)
  );
  rstmgr_cnsty_chk_if rstmgr_cnsty_chk_if ();

  logic sw_rst_req_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sw_rst_req_q <= '0;
    end else if (sw_rst_req_q && rstmgr_cnsty_chk_if.sw_rst_req_clr_o) begin
      sw_rst_req_q <= '0;
    end else if (!sw_rst_req_q && rstmgr_cnsty_chk_if.sw_rst_req_i &&
                 !rstmgr_cnsty_chk_if.sw_rst_req_clr_o) begin
      sw_rst_req_q <= 1'b1;
    end
  end

  logic leaf_chk_rst_n;
  prim_rst_sync u_prim_rst_sync (
    .clk_i      (child_clk_i),
    .d_i        (rst_ni),
    .q_o        (leaf_chk_rst_n),
    .scan_rst_ni(1'b1),
    .scanmode_i(prim_mubi_pkg::MuBi4False)
  );

  rstmgr_cnsty_chk dut (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .child_clk_i(child_clk_i),
    .child_rst_ni(rstmgr_cnsty_chk_if.child_rst_ni),
    .child_chk_rst_ni(leaf_chk_rst_n),
    .parent_rst_ni(rstmgr_cnsty_chk_if.parent_rst_ni),
    .sw_rst_req_i(rstmgr_cnsty_chk_if.sw_rst_req_i | sw_rst_req_q),
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
