// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class irq_seq_item extends uvm_sequence_item;

  rand bit          irq_software;
  rand bit          irq_timer;
  rand bit          irq_external;
  rand bit [14:0]   irq_fast;
  rand bit          irq_nm;
  rand int          num_of_interrupt;

  constraint num_of_interrupt_c {
    num_of_interrupt inside {[0:DATA_WIDTH-1]};
    $countones({irq_software, irq_timer, irq_external, irq_fast, irq_nm}) == num_of_interrupt;
  }

  constraint bring_up_c {
    soft num_of_interrupt == 1;
  }

  `uvm_object_utils_begin(irq_seq_item)
    `uvm_field_int(irq_software, UVM_DEFAULT)
    `uvm_field_int(irq_timer,    UVM_DEFAULT)
    `uvm_field_int(irq_external, UVM_DEFAULT)
    `uvm_field_int(irq_fast,     UVM_DEFAULT)
    `uvm_field_int(irq_nm,       UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : irq_seq_item
