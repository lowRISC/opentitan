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
  `uvm_component_new

  bit under_reset;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    alert_esc_port = new("alert_esc_port", this);
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    wait_for_reset_done();
  endtask : run_phase

  virtual task wait_for_reset_done();
    @(posedge cfg.vif.rst_n);
  endtask : wait_for_reset_done

  virtual task reset_thread();
    forever begin
      @(negedge cfg.vif.rst_n);
      under_reset = 1;
      @(posedge cfg.vif.rst_n);
      // reset signals at posedge rst_n to avoid race condition at negedge rst_n
      reset_signals();
      under_reset = 0;
    end
  endtask : reset_thread

  // this function can be used in derived classes to reset local signals/variables if needed
  virtual function void reset_signals();
    cfg.under_ping_handshake = 0;
  endfunction

endclass
