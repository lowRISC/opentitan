// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert sender receiver interface base monitor
// ---------------------------------------------

class alert_esc_base_monitor extends dv_base_monitor #(
  .ITEM_T(alert_esc_seq_item),
  .CFG_T (alert_esc_agent_cfg),
  .COV_T (alert_esc_agent_cov)
);

  `uvm_component_utils(alert_esc_base_monitor)
  uvm_analysis_port #(alert_esc_seq_item) alert_esc_port;

  bit under_reset;

  extern function new (string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task wait_for_reset_done();
  extern virtual task reset_thread();
  // this function can be used in derived classes to reset local signals/variables if needed
  extern virtual function void reset_signals();

endclass : alert_esc_base_monitor

function alert_esc_base_monitor::new (string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void alert_esc_base_monitor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  alert_esc_port = new("alert_esc_port", this);
endfunction : build_phase

task alert_esc_base_monitor::run_phase(uvm_phase phase);
  wait_for_reset_done();
endtask : run_phase

task alert_esc_base_monitor::wait_for_reset_done();
  @(posedge cfg.vif.rst_n);
endtask : wait_for_reset_done

task alert_esc_base_monitor::reset_thread();
  forever begin
    @(negedge cfg.vif.rst_n);
    under_reset = 1;
    @(posedge cfg.vif.rst_n);
    // reset signals at posedge rst_n to avoid race condition at negedge rst_n
    reset_signals();
    under_reset = 0;
  end
endtask : reset_thread

function void alert_esc_base_monitor::reset_signals();
  cfg.under_ping_handshake = 0;
endfunction
