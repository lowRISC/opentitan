// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_monitor extends dv_base_monitor #(
    .ITEM_T (jtag_item),
    .CFG_T  (jtag_agent_cfg),
    .COV_T  (jtag_agent_cov)
  );
  `uvm_component_utils(jtag_monitor)

  // the base class provides the following handles for use:
  // jtag_agent_cfg: cfg
  // jtag_agent_cov: cov
  // uvm_analysis_port #(jtag_item): analysis_port

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
  endtask

  // collect transactions forever - already forked in dv_base_moditor::run_phase
  virtual protected task collect_trans(uvm_phase phase);
    forever begin
      // TODO: detect event

      // TODO: sample the interface

      // TODO: sample the covergroups

      // TODO: write trans to analysis_port

      // TODO: remove the line below: it is added to prevent zero delay loop in template code
      #1us;
    end
  endtask

endclass
