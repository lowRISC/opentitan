// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_driver extends dv_base_driver #(spi_item, spi_agent_cfg);
  `uvm_component_utils(spi_driver)
  `uvm_component_new

  virtual task get_and_drive();
    `uvm_fatal(`gfn, "this is implemented as pure virtual task - please extend")
  endtask

endclass
