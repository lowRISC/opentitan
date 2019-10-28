// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_monitor extends dv_base_monitor #(
    .ITEM_T (i2c_item),
    .CFG_T  (i2c_agent_cfg),
    .COV_T  (i2c_agent_cov)
  );
  `uvm_component_utils(i2c_monitor)

  // the base class provides the following handles for use:
  i2c_agent_cfg  cfg;
  i2c_agent_cov  cov;
  i2c_item       host_item;
  i2c_item       device_item;

  // analize ports
  uvm_analysis_port #(i2c_item) host_analysis_port;
  uvm_analysis_port #(i2c_item) device_analysis_port;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    host_analysis_port = new("host_analysis_port", this);
    device_analysis_port = new("device_analysis_port", this);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    //collect_trans(phase)
  endtask

  // collect transactions forever - already forked in dv_base_moditor::run_phase
  virtual protected task collect_trans(uvm_phase phase);
    i2c_item item;
    forever begin
      // TODO: detect event

      // TODO: sample the interface

      // TODO: sample the covergroups

      // TODO: write trans to analysis_port

      // TODO: remove the line below: it is added to prevent zero delay loop in template code
      #1us;
    end
  endtask : collect_trans

endclass : i2c_monitor
