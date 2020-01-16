// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_monitor extends dv_base_monitor #(
  .ITEM_T (usb20_item),
  .CFG_T  (usb20_agent_cfg),
  .COV_T  (usb20_agent_cov)
);
  `uvm_component_utils(usb20_monitor)

  // the base class provides the following handles for use:
  // usb20_agent_cfg: cfg
  // usb20_agent_cov: cov
  // uvm_analysis_port #(usb20_item): analysis_port

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
