// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_item extends uvm_sequence_item;
  bit  data_q[$];
  //uint length;

  `uvm_object_utils_begin(pattgen_item);
    //`uvm_field_int(length,       UVM_DEFAULT | UVM_NOCOMPARE)
    `uvm_field_queue_int(data_q, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : pattgen_item
