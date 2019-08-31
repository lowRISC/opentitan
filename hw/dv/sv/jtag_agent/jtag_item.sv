// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_item extends uvm_sequence_item;

  // random variables
  rand uint addr_len;
  rand uint data_len;

  rand logic [JTAG_IRW-1:0] addr;   // address
  rand logic [JTAG_DRW-1:0] data;   // data written or read
  rand logic                write;  // write signal

  constraint addr_len_c {
    addr_len <= JTAG_IRW;
  }

  constraint data_len_c {
    data_len <= JTAG_DRW;
  }

  `uvm_object_utils_begin(jtag_item)
    `uvm_field_int(addr_len,  UVM_DEFAULT)
    `uvm_field_int(data_len,  UVM_DEFAULT)
    `uvm_field_int(addr,      UVM_DEFAULT)
    `uvm_field_int(data,      UVM_DEFAULT)
    `uvm_field_int(write,     UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
