// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Esc sender driver
// ---------------------------------------------
class esc_sender_driver extends alert_esc_base_driver;

  `uvm_component_utils(esc_sender_driver)

  `uvm_component_new

  virtual task reset_signals();
    do_reset();
    forever begin
      @(negedge cfg.vif.rst_n);
      under_reset = 1;
      do_reset();
      @(posedge cfg.vif.rst_n);
      under_reset = 0;
    end
  endtask

  virtual task get_and_drive();
    // TODO
    drive_esc();
  endtask : get_and_drive

  virtual task drive_esc();
    // TODO
    wait(!under_reset);
  endtask

  virtual task do_reset();
    cfg.vif.esc_tx_int.esc_p <= 1'b0;
    cfg.vif.esc_tx_int.esc_n <= 1'b1;
  endtask
endclass : esc_sender_driver

