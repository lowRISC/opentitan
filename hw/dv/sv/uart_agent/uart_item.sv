// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_item extends uvm_sequence_item;

  // start and stop bits
  rand bit start_bit = 1'b0;
  rand bit stop_bit = 1'b1;

  // byte of data sent or received
  rand bit [7:0] data;

  // calculated parity of data sent or received
  rand bit parity;

  // allow driver to override sending parity
  rand bit ovrd_en_parity = 1'b0;

  // dont override start_bit unless testing an error scenario
  constraint start_bit_c {
    start_bit == 1'b0;
  }

  // dont override stop_bit unless testing an error scenario
  constraint stop_bit_c {
    stop_bit == 1'b1;
  }

  // dont override parity setting unless testing an error scenario
  constraint ovrd_en_parity_c {
    ovrd_en_parity == 1'b0;
  }

  `uvm_object_utils_begin(uart_item)
    `uvm_field_int(start_bit,       UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPRINT)
    `uvm_field_int(data,            UVM_DEFAULT)
    // parity & stop_bit are checked in monitor
    `uvm_field_int(parity,          UVM_DEFAULT | UVM_NOCOMPARE)
    `uvm_field_int(stop_bit,        UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPRINT)
    `uvm_field_int(ovrd_en_parity,  UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPRINT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
