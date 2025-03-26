// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_data_driver extends dv_base_driver #(
  .ITEM_T(uvm_sequence_item),
  .CFG_T(gpio_data_agent_cfg));

  `uvm_component_utils(gpio_data_driver)

  // Constructor: Creates a new instance of the gpio_driver class
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    // Overrided run_phase
  endtask

endclass
