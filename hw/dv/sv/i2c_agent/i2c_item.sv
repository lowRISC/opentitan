// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_item extends uvm_sequence_item;

  // byte of data sent or received
  rand logic [`I2C_FMT_FIFO_WIDTH-1:0] data[$];

  // constrain size of data sent / received to be at most 64kB
  constraint data_size_c {
    data.size() inside {[1:65536]};
  }

  `uvm_object_utils_begin(i2c_item)
    `uvm_field_queue_int(data, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : i2c_item
