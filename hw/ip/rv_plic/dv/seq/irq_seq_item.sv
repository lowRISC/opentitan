// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

class irq_seq_item #(int src = 32) extends uvm_sequence_item;

  bit [$clog2(src+1)-1:0] irq_id ;

  `uvm_object_utils_begin(irq_seq_item)
    `uvm_field_int (irq_id, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "irq_seq_item");
    super.new(name);
  endfunction : new

endclass : irq_seq_item
