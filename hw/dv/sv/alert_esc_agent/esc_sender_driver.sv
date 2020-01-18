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

  virtual task get_and_drive();
    // TODO
  endtask : get_and_drive

endclass : esc_sender_driver

