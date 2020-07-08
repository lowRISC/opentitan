// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_driver extends spi_driver;
  `uvm_component_utils(spi_device_driver)
  `uvm_component_new

  virtual task reset_signals();
    forever begin
      @(negedge cfg.vif.rst_n);
      under_reset = 1'b1;
      cfg.vif.sdo <= 1'b0;
      @(posedge cfg.vif.rst_n);
      under_reset = 1'b0;
    end
  endtask

  // TODO:
  virtual task get_and_drive();
  endtask

endclass
