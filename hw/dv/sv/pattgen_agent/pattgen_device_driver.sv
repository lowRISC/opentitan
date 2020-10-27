// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_device_driver extends pattgen_driver;
  `uvm_component_utils(pattgen_device_driver)
  `uvm_component_new

  virtual task get_and_drive();
    @(posedge cfg.vif.rst_ni);
    // keep this as very simple task since pattgen DUT
    // does not require responses from pattgen_agent
  endtask : get_and_drive

endclass : pattgen_device_driver