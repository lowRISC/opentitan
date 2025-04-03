// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Esc sender driver
// ---------------------------------------------
class esc_sender_driver extends alert_esc_base_driver;

  `uvm_component_utils(esc_sender_driver)


  extern function new (string name="", uvm_component parent=null);
  extern virtual task reset_signals();
  extern virtual task get_and_drive();
  extern virtual task drive_esc();
  extern virtual task do_reset();

endclass : esc_sender_driver

function esc_sender_driver::new (string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

task esc_sender_driver::reset_signals();
  do_reset();
  forever begin
    @(negedge cfg.vif.rst_n);
    under_reset = 1;
    do_reset();
    @(posedge cfg.vif.rst_n);
    under_reset = 0;
  end
endtask : reset_signals

task esc_sender_driver::get_and_drive();
  // LC_CTRL uses virtual interface to directly drive escalation requests.
  // Other escalation handshakes are checked in prim_esc direct sequence.
  // So the following task is not implemented.
  drive_esc();
endtask : get_and_drive

task esc_sender_driver::drive_esc();
  // LC_CTRL uses virtual interface to directly drive escalation requests.
  // Other escalation handshakes are checked in prim_esc direct sequence.
  // So this task is not implemented.
  wait(!under_reset);
endtask : drive_esc

task esc_sender_driver::do_reset();
  cfg.vif.esc_tx_int.esc_p <= 1'b0;
  cfg.vif.esc_tx_int.esc_n <= 1'b1;
endtask : do_reset
