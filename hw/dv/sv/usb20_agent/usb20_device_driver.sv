// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_device_driver extends usb20_driver;
  `uvm_component_utils(usb20_device_driver)

  // the base class provides the following handles for use:
  // usb20_agent_cfg: cfg

  `uvm_component_new

  // drive trans received from sequencer
  virtual task get_and_drive();
  endtask

endclass
