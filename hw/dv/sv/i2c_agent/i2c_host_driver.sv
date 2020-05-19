// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_host_driver extends i2c_driver;
  `uvm_component_utils(i2c_host_driver)
  `uvm_component_new

  // TODO:
  virtual task reset_signals();
  endtask : reset_signals

  // TODO:
  virtual task get_and_drive();
  endtask

endclass : i2c_host_driver
