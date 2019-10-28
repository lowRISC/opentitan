// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_item extends uvm_sequence_item;

  // byte of data sent or received
  rand logic [`I2C_FMT_FIFO_WIDTH-1:0] data[$];

  // random variable and their constrains
  rand bit rd_data;
  rand int max_host_rd_byte;    // max read data requested by host
  rand int max_host_wr_byte;    // max write data sent by host
  rand int dly_to_send_nack;
  rand int dly_to_send_ack;
  rand int dly_to_send_stop;
  rand int dly_to_send_rd_data;
  rand int dly_to_back_to_back;

  constraint rd_data_c {
    rd_data inside {[0:1]};
  }

  constraint max_host_rd_byte_c {
    max_host_rd_byte inside {[1:30]};
  }

  constraint max_host_wr_byte_c {
    max_host_wr_byte inside {[1:30]};
  }

  constraint dly_to_send_ack_c {
    dly_to_send_ack inside {[1:5]};
  }

  constraint dly_to_send_nack_c {
    dly_to_send_nack inside {[1:5]};
  }

  constraint dly_to_send_stop_c {
    dly_to_send_stop inside {[1:5]};
  }

  constraint dly_to_send_rd_data_c {
    dly_to_send_rd_data inside {[1:5]};
  }

  constraint dly_to_back_to_back_c {
    dly_to_back_to_back inside {[1:10]};
  }

  // constrain size of data sent / received to be at most 64kB
  constraint data_size_c {
    data.size() inside {[1:65536]};
  }

  `uvm_object_utils_begin(i2c_item)
    `uvm_field_queue_int(data, UVM_DEFAULT)
    `uvm_field_int(max_host_rd_byte,    UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPRINT)
    `uvm_field_int(max_host_wr_byte,    UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPRINT)
    `uvm_field_int(dly_to_send_ack,     UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPRINT)
    `uvm_field_int(dly_to_send_nack,    UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPRINT)
    `uvm_field_int(dly_to_send_stop,    UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPRINT)
    `uvm_field_int(dly_to_send_rd_data, UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPRINT)
    `uvm_field_int(dly_to_back_to_back, UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPRINT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : i2c_item
