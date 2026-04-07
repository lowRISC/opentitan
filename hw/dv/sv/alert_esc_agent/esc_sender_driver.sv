// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Escalation sender driver

class esc_sender_driver extends dv_base_driver#(alert_esc_seq_item, alert_esc_agent_cfg);
  `uvm_component_utils(esc_sender_driver)

  extern function new (string name, uvm_component parent);
  extern virtual task reset_signals();
  extern virtual task get_and_drive();

  extern local task reset_esc();
endclass : esc_sender_driver

function esc_sender_driver::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

task esc_sender_driver::reset_signals();
  wait(cfg.vif.rst_n !== 1'b1);
  forever begin
    under_reset = 1;
    reset_esc();
    wait(cfg.vif.rst_n === 1'b1);
    under_reset = 0;

    wait(cfg.vif.rst_n !== 1'b1);
  end
endtask : reset_signals

task esc_sender_driver::get_and_drive();
  // LC_CTRL uses virtual interface to directly drive escalation requests.
  // Other escalation handshakes are checked in prim_esc direct sequence.
  // So the following task is not implemented.
  wait(!under_reset);
endtask : get_and_drive

task esc_sender_driver::reset_esc();
  cfg.vif.esc_tx_int.esc_p <= 1'b0;
  cfg.vif.esc_tx_int.esc_n <= 1'b1;
endtask : reset_esc
