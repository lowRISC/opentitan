// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class reset_driver extends dv_base_driver #(
  .ITEM_T(reset_item),
  .CFG_T (reset_agent_cfg)
);
  `uvm_component_utils(reset_driver)

  // Standard SV/UVM methods
  extern function new(string name, uvm_component parent = null);
  extern task pre_reset_phase(uvm_phase phase);
  extern task reset_phase(uvm_phase phase);

  // Parent methods
  extern virtual task reset_signals();
  extern virtual task get_and_drive();
  extern virtual task drive_trans(reset_item tr);
  extern task hold_state(reset_phase_e reset_phase, int unsigned waiting_time);
  extern task drive_reset(reset_phase_e reset_phase);
endclass : reset_driver


function reset_driver::new(string name, uvm_component parent = null);
  super.new(name, parent);
endfunction : new

task reset_driver::pre_reset_phase(uvm_phase phase);
  cfg.vif.drive_idle(cfg.polarity);
endtask : pre_reset_phase

task reset_driver::reset_phase(uvm_phase phase);
  reset_item tr;

  phase.raise_objection(this);
  // Build the initial transaction as the first reset should occur from the reset_phase
  tr = reset_item::type_id::create("tr");
  if (!tr.randomize() with {
    assert_delay == cfg.ini_assert_delay;
    assert_width == cfg.ini_assert_width;
  }) `uvm_fatal(`gfn, "Failed to randomize transaction !")
  drive_trans(tr);
  phase.drop_objection(this);
endtask : reset_phase

task reset_driver::reset_signals();
  // Requires to be overriden but can remain empty for this particular agent
endtask : reset_signals

task reset_driver::get_and_drive();
  reset_item tr;

  forever begin
    seq_item_port.get_next_item(tr);
    drive_trans(tr);
    seq_item_port.item_done();
  end
endtask : get_and_drive

task reset_driver::drive_trans(reset_item tr);
  // Wait a certain amount of time before asserting the reset
  hold_state(Assertion, tr.assert_delay);

  // Assert reset
  drive_reset(Assertion);

  // Keep the reset active for a certain amount of time before deasserting it
  hold_state(Deassertion, tr.assert_width);

  // Deassert reset
  drive_reset(Deassertion);
endtask : drive_trans

task reset_driver::hold_state(reset_phase_e reset_phase, int unsigned waiting_time);
  bit     is_sync;
  string  time_unit;

  if (reset_phase == Assertion) begin
    is_sync = cfg.assert_is_sync;
  end else begin
    is_sync = cfg.deassert_is_sync;
  end

  if (is_sync) begin
    time_unit = "clock cycle(s)";
  end else begin
    time_unit = "ns";
  end

  if (waiting_time > 0) begin
    if (cfg.enable_debug_messages) begin
      `uvm_info(`gtn, $sformatf("Wait %0d %0s before reset %0s",
        waiting_time, time_unit, reset_phase.name()), UVM_LOW)
    end
    if (is_sync) begin
      repeat (waiting_time) @(posedge cfg.vif.clk_i);
    end else begin
      #(waiting_time*1ns);
    end
  end
endtask : hold_state

task reset_driver::drive_reset(reset_phase_e reset_phase);
  if (cfg.enable_debug_messages) begin
    `uvm_info(`gtn, $sformatf("Reset %0s", reset_phase.name()), UVM_LOW)
  end
  if ((reset_phase == Assertion   && cfg.polarity == ActiveLow) ||
      (reset_phase == Deassertion && cfg.polarity == ActiveHigh)) begin
    cfg.vif.rst_o  <= 1'b0;
  end else begin
    cfg.vif.rst_o  <= 1'b1;
  end
endtask : drive_reset
