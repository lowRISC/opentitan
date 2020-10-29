// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_driver #(parameter int HostDataWidth = 32,
                         parameter int DeviceDataWidth = HostDataWidth)
  extends dv_base_driver #(
    .ITEM_T(push_pull_item#(HostDataWidth, DeviceDataWidth)),
    .CFG_T(push_pull_agent_cfg#(HostDataWidth, DeviceDataWidth))
);

  bit in_reset = 1'b0;

  `uvm_component_param_utils(push_pull_driver#(HostDataWidth, DeviceDataWidth))
  `uvm_component_new

  virtual task reset_signals();
    // initial reset at start of test
    do_reset();
    forever begin
      @(negedge cfg.vif.rst_n);
      `uvm_info(`gfn, "driver is resetting", UVM_HIGH)
      in_reset = 1'b1;
      do_reset();
      @(posedge cfg.vif.rst_n);
      `uvm_info(`gfn, "driver is out of reset", UVM_HIGH)
      in_reset = 1'b0;
    end
  endtask

  virtual task do_reset();
    `uvm_fatal(`gfn, "Must implement in host/device driver")
  endtask

  virtual task drive_pull();
    `uvm_fatal(`gfn, "Must implement in host/device driver")
  endtask

  virtual task drive_push();
    `uvm_fatal(`gfn, "Must implement in host/device driver")
  endtask

endclass
