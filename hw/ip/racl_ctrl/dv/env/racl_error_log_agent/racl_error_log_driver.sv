// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A driver for an error log interface. This behaves as a set of subscribers to racl_ctrl and
// reports errors.

class racl_error_log_driver extends dv_base_driver #(.ITEM_T (racl_error_log_vec_driver_item),
                                                     .CFG_T  (racl_error_log_agent_cfg));
  `uvm_component_utils(racl_error_log_driver)

  // The interface that gets driven. This is set up by the agent in the build phase.
  virtual racl_error_log_if vif;

  extern function new (string name, uvm_component parent);

  // Drive items received from the sequencer. This runs forever implementing a task declared in
  // dv_base_driver.
  extern task get_and_drive();

  // Watch for resets, clearing the error log signals when one is asserted. This runs forever
  // implementing a task declared in dv_base_driver.
  extern task reset_signals();

  // Drive this item over the interface.
  //
  // If this task starts in reset, it clears the error log input, then waits until reset is cleared
  // before driving the item. It returns immediately (not sending the errors) if reset is asserted
  // in the middle of the delay.
  extern local task drive_item(racl_error_log_vec_driver_item item);

  // Reset all the signals in the interface
  //
  // This is used on reset so drives the interface signals directly (instead of using a clocking
  // block)
  extern local task reset_lines();

  // Clear the error log signal from subscriber i
  //
  // The valid signal is set to 0 and all other signals are set to 'x.
  extern local task clear_line(int unsigned i);

  // Set the error log signal from subscriber i to the values from item
  extern local task set_line(int unsigned i, racl_error_log_item item);
endclass

function racl_error_log_driver::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

task racl_error_log_driver::get_and_drive();
  if (vif == null) `uvm_fatal(`gfn, "Cannot drive items with no vif.")

  forever begin
    racl_error_log_vec_driver_item item;
    seq_item_port.get_next_item(item);
    drive_item(item);
    seq_item_port.item_done();
  end
endtask

task racl_error_log_driver::reset_signals();
  forever begin
    wait(!vif.rst_ni);
    reset_lines();
    wait(vif.rst_ni);
  end
endtask

task racl_error_log_driver::drive_item(racl_error_log_vec_driver_item item);
  if (!vif.rst_ni) begin
    vif.subscriber_cb.errors <= '0;
    wait(vif.rst_ni);
  end

  vif.wait_ctrl_clks_or_rst(item.delay);
  if (!vif.rst_ni) return;

  // Drive the relevant errors to the pins
  for (int i = 0; i < 63; i++)
    if (item.errors.exists(i)) set_line(i, item.errors[i]); else clear_line(i);

  // Wait one cycle. racl_ctrl will see the error(s) on the clock edge.
  vif.wait_ctrl_clks_or_rst(1);
  if (!vif.rst_ni) return;

  // Now clear everything again. Don't wait another cycle: if the next item has a zero delay, it
  // will be back-to-back with this one.
  for (int i = 0; i < 63; i++) clear_line(i);
endtask

task racl_error_log_driver::reset_lines();
  // Reset the signals through subscriber_cb as well as the raw signals. This ensures that we clear
  // any "pending value" that was written on the final clock edge before reset.

  vif.errors <= 'x;
  vif.subscriber_cb.errors <= 'x;

  for (int i = 0; i < 63; i++) begin
    vif.errors[i].valid <= 1'b0;
    vif.subscriber_cb.errors[i].valid <= 1'b0;
  end
endtask

task racl_error_log_driver::clear_line(int unsigned i);
  vif.subscriber_cb.errors[i] <= 'x;
  vif.subscriber_cb.errors[i].valid <= 1'b0;
endtask

task racl_error_log_driver::set_line(int unsigned i, racl_error_log_item item);
  vif.subscriber_cb.errors[i].valid           <= 1'b1;
  vif.subscriber_cb.errors[i].overflow        <= item.overflow;
  vif.subscriber_cb.errors[i].racl_role       <= item.role;
  vif.subscriber_cb.errors[i].ctn_uid         <= item.ctn_uid;
  vif.subscriber_cb.errors[i].read_access     <= item.read_not_write;
  vif.subscriber_cb.errors[i].request_address <= item.request_address;
endtask
