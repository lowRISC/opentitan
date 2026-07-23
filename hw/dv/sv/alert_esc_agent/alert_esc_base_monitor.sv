// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// A base class for monitors that track alert/escalation items and watch an alert_esc_if.

class alert_esc_base_monitor extends dv_reactive_monitor #(
  .ITEM_T(alert_esc_seq_item),
  .CFG_T (alert_esc_agent_cfg),
  .COV_T (alert_esc_agent_cov)
);

  `uvm_component_utils(alert_esc_base_monitor)

  // An output port that reports alert items that have been seen. If this is an esc_monitor, it will
  // be null.
  uvm_analysis_port #(alert_seq_item) m_alert_port;

  // An output port that reports escalation items that have been seen. If this is an alert_monitor,
  // it will be null.
  uvm_analysis_port #(esc_seq_item) m_esc_port;

  extern function new(string name, uvm_component parent);
  extern virtual task run_phase(uvm_phase phase);

  // Reset config flags to their initial values (at the end of a reset)
  extern local function void reset_signals();
endclass : alert_esc_base_monitor

function alert_esc_base_monitor::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

task alert_esc_base_monitor::run_phase(uvm_phase phase);
  fork
    super.run_phase(phase);
    begin
      // Make sure that in_reset is correct at the start of the phase, then check that we are
      // genuinely in reset by the start of the loop.
      cfg.in_reset = (cfg.vif.rst_n !== 1'b1);
      wait(!cfg.vif.rst_n);

      forever begin
        cfg.in_reset = 1;
        wait (cfg.vif.rst_n);

        // reset signals at posedge rst_n to avoid race condition at negedge rst_n
        reset_signals();
        cfg.in_reset = 0;

        wait (!cfg.vif.rst_n);
      end
    end
  join
endtask : run_phase

function void alert_esc_base_monitor::reset_signals();
  cfg.under_ping_handshake = 0;
endfunction
