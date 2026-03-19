// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// A base class for a monitor that tracks alert/escalation items, watching an alert_esc_if.

class alert_esc_base_monitor extends dv_base_monitor #(
  .ITEM_T(alert_esc_seq_item),
  .CFG_T (alert_esc_agent_cfg),
  .COV_T (alert_esc_agent_cov)
);

  `uvm_component_utils(alert_esc_base_monitor)

  // The output port that reports alert/escalation items that have been seen
  uvm_analysis_port #(alert_esc_seq_item) alert_esc_port;

  extern function new (string name, uvm_component parent);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

  // Reset config flags to their initial values (at the end of a reset)
  extern local function void reset_signals();
endclass : alert_esc_base_monitor

function alert_esc_base_monitor::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void alert_esc_base_monitor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  alert_esc_port = new("alert_esc_port", this);
endfunction

task alert_esc_base_monitor::run_phase(uvm_phase phase);
  fork
    super.run_phase(phase);
    begin
      forever begin
        cfg.in_reset = 1;
        wait(cfg.vif.rst_n);

        // reset signals at posedge rst_n to avoid race condition at negedge rst_n
        reset_signals();
        cfg.in_reset = 0;

        wait(!cfg.vif.rst_n);
      end
    end
  join
endtask

function void alert_esc_base_monitor::reset_signals();
  cfg.under_ping_handshake = 0;
endfunction
