// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${name}_device_driver extends ${name}_driver;
  `uvm_component_utils(${name}_device_driver)

  // the base class provides the following handles for use:
  // ${name}_agent_cfg: cfg

  `uvm_component_new

  // drive trans received from sequencer
  virtual task get_and_drive();
  endtask

endclass
