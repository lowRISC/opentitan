// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert sender receiver interface base monitor
// ---------------------------------------------

class alert_esc_base_monitor extends dv_base_monitor#(
    .ITEM_T (alert_esc_seq_item),
    .CFG_T  (alert_esc_agent_cfg),
    .COV_T  (alert_esc_agent_cov)
  );

  `uvm_component_utils(alert_esc_base_monitor)
  uvm_analysis_port #(alert_esc_seq_item) alert_esc_port;
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    alert_esc_port = new("alert_esc_port", this);
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    // TODO: implement the run phase
  endtask : run_phase

endclass
